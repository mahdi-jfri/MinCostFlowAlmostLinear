module

public import MinCostFlow.Machine.WideWord.LSSTProgramStages
import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# LSSTProgramSim, first part

The first part of `LSSTProgramSim.lean`, split off to keep files short. It contains:
- Small list helpers
- General branch stage 2: weights, encodeGAug, `[AN19]`, simDecode
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Small list helpers -/

private lemma list_map_sum_le {α : Type*} (l : List α) (f : α → ℕ) (M : ℕ)
    (h : ∀ x ∈ l, f x ≤ M) : (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    exact le_trans
      (Nat.add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx)))
      (le_of_eq (Nat.add_comm _ _))

private lemma unsignedVal_congr {m₁ m₂ : ℕ → ℕ} {a h L : ℕ}
    (hm : ∀ q < L, m₂ (a + q) = m₁ (a + q)) :
    Num.unsignedVal m₂ a h L = Num.unsignedVal m₁ a h L := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    dsimp only [Num.unsignedVal]
    have h0 := hm 0 (Nat.zero_lt_succ L)
    rw [Nat.add_zero] at h0
    have hrest := ih (a := a + 1) fun q hq => by
      rw [Nat.add_assoc a 1 q, Nat.add_comm 1 q]
      exact hm (q + 1) (Nat.succ_lt_succ hq)
    rw [h0, hrest]

private lemma numValid_fixVal_congr {m₁ m₂ : ℕ → ℕ} {a h L P_fp : ℕ}
    (hv : Num.Valid m₁ a h L) (hm : ∀ q < L, m₂ (a + q) = m₁ (a + q)) :
    Num.Valid m₂ a h L ∧ Num.fixVal m₂ a h L P_fp = Num.fixVal m₁ a h L P_fp := by
  refine ⟨fun i hi => by rw [hm i hi]; exact hv i hi, ?_⟩
  dsimp only [Num.fixVal, Num.intVal]
  rw [unsignedVal_congr hm]

private lemma mem_inactiveVertsList_lt {n : ℕ} {V_list : List ℕ} {x : ℕ}
    (hx : x ∈ inactiveVertsList n V_list) : x < n :=
  (mem_inactiveVertsList_iff.mp hx).1

private lemma decodeAN19Output_orig_lt (G : IndexedGraph) (V_list B : List ℕ)
    (mult : ℕ → ℕ) (out : List ℕ) :
    ∀ e ∈ (decodeAN19Output G V_list B mult out).1, e < G.m := by
  intro x hx
  dsimp only [decodeAN19Output] at hx
  rw [List.mem_map] at hx
  obtain ⟨j, hjf, rfl⟩ := hx
  have hj_lt : j < ((nonloopEdges G).map mult).sum := by simpa using (List.mem_filter.mp hjf).2
  have hlen : (origOfCopy G mult).length = ((nonloopEdges G).map mult).sum :=
    (origOfCopy_length G mult).trans (copyEdgeList_length G mult)
  have hj_len : j < (origOfCopy G mult).length := hlen ▸ hj_lt
  rw [List.getD_eq_getElem _ _ hj_len]
  have hx_mem : (origOfCopy G mult)[j]'hj_len ∈ origOfCopy G mult := List.getElem_mem hj_len
  dsimp only [origOfCopy] at hx_mem
  rw [List.mem_flatMap] at hx_mem
  obtain ⟨e, he, hrep⟩ := hx_mem
  rw [List.mem_replicate] at hrep
  have heq_j : (origOfCopy G mult)[j]'hj_len = e := hrep.2
  rw [heq_j]
  exact (mem_nonloopEdges_iff.mp he).1

private lemma decodeAN19Output_len_le (G : IndexedGraph) (V_list B : List ℕ)
    (mult : ℕ → ℕ) (out : List ℕ)
    (hout : out.length = V_list.length - 1)
    (hV_pos : 0 < V_list.length)
    (hVI : V_list.length + (inactiveVertsList G.n V_list).length ≤ G.n) :
    (decodeAN19Output G V_list B mult out).1.length +
      (decodeAN19Output G V_list B mult out).2.length ≤ G.n - 1 := by
  let m₁ := ((nonloopEdges G).map mult).sum
  have hsum_disj : ∀ (L : List ℕ) (p q : ℕ → Bool), (∀ x, ¬ (p x = true ∧ q x = true)) →
      (L.filter p).length + (L.filter q).length ≤ L.length := by
    intro L p q hdisj
    induction L with
    | nil => simp
    | cons y ys ih =>
      dsimp only [List.filter]
      by_cases hp : p y = true <;> by_cases hq : q y = true
      · exact absurd ⟨hp, hq⟩ (hdisj y)
      · simp [hp, hq]; omega
      · simp [hp, hq]; omega
      · simp [hp, hq]; omega
  have hf_disj := hsum_disj out (fun j => decide (j < m₁))
    (fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length))
    (fun x ⟨h1, h2⟩ => by simp at h1 h2; omega)
  dsimp only [decodeAN19Output]
  dsimp only [m₁] at hf_disj
  rw [List.length_append, List.length_map, List.length_map, List.length_map]
  omega

/-! ### General branch stage 2: weights, encodeGAug, `[AN19]`, simDecode -/

lemma lsst_weights_sim_runs_tail {w h b c_AN : ℕ} {P Q_AN : Program} {ω : ℕ → Bool}
    {mem_orig : ℕ → ℕ} {st : State} {k T : ℕ}
    (K_AN : ℝ)
    (hp : P.HasAt b (lsstModule Q_AN b h))
    (hAN : ∀ (G_a : Cited.WGraph), G_a.graph.IsValid → G_a.graph.IsLoopless → G_a.IsConnected →
      (∀ e ∈ G_a.edges, 1 ≤ e.2.2) →
      ∃ out cost,
        WordRAM.RunsTo (WordRAM.wordSize c_AN G_a.encode) Q_AN G_a.encode (fun _ => false) out cost ∧
          G_a.IsSpanningTree out ∧
          G_a.totalStretch out ≤ K_AN * G_a.m * Cited.logLogFactor G_a.n ∧
          (cost : ℝ) ≤ K_AN * (G_a.m + 1) * (Cited.logLogFactor G_a.n + Cited.weightFactor G_a.n G_a.maxWeight))
    (G : IndexedGraph) (v ℓ : ℕ → ℝ) (P_fp : ℕ)
    (tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap : ℕ)
    (B : List ℕ) (newHeap vListPtr inactPtr bPtr bfsHeap : ℕ)
    (hc_pos : 1 ≤ c_AN) (hG : G.Valid) (h1 : 1 ≤ h) (hw : 3 * h + 2 ≤ w) (hL1 : 1 ≤ L)
    (hLsim : lsstLSimMin c_AN G.n G.m L h ≤ L_sim)
    (hnl_ne : (nonloopEdges G).length ≠ 0)
    (ht_lt : tailArr + G.m ≤ heap) (hh_lt : headArr + G.m ≤ heap)
    (hlen_lt : lenArr + G.m * L ≤ heap) (hwt_lt : wtArr + G.m * L ≤ heap)
    (hoo_lt : outOrigPtr + G.n ≤ heap) (hob_lt : outBridgePtr + 2 * G.n ≤ heap)
    (hoh_lt : outHdrPtr + 2 ≤ heap)
    (hd_ob : DisjointRanges outOrigPtr G.n outBridgePtr (2 * G.n))
    (hd_oh : DisjointRanges outOrigPtr G.n outHdrPtr 2)
    (hd_bh : DisjointRanges outBridgePtr (2 * G.n) outHdrPtr 2)
    (htail_orig : ListAt mem_orig tailArr (List.ofFn fun i : Fin G.m => G.tail i))
    (hhead_orig : ListAt mem_orig headArr (List.ofFn fun i : Fin G.m => G.head i))
    (hlen_orig : ∀ e < G.m, Num.Valid mem_orig (lenArr + e * L) h L ∧
      Num.fixVal mem_orig (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e)
    (hwt_orig : ∀ e < G.m, Num.Valid mem_orig (wtArr + e * L) h L ∧
      Num.fixVal mem_orig (wtArr + e * L) h L P_fp = v e ∧ 0 < v e)
    (hheap_space : heap + lsstSpace Q_AN K_AN G.n G.m L_sim h < 2 ^ w)
    (hnew : newHeap = heap + G.m + 3 + 5 * G.n + 2 * (nonloopEdges G).length)
    (hvL : vListPtr = heap + G.m + 2)
    (hinP : inactPtr = vListPtr + G.n)
    (hbP : bPtr = newHeap + G.n)
    (hbfsP : bfsHeap = bPtr + G.n)
    (hB_le : B.length ≤ (activeVertsList G).length)
    (hrg : LSSTInRegs st G.n G.m tailArr headArr lenArr wtArr L L_sim outOrigPtr outBridgePtr outHdrPtr heap)
    (hr20 : st.regs 20 = (nonloopEdges G).length)
    (hr22 : st.regs 22 = newHeap)
    (hr23 : st.regs 23 = (activeVertsList G).length)
    (hr24 : st.regs 24 = (inactiveVertsList G.n (activeVertsList G)).length)
    (hr26 : st.regs 26 = inactPtr)
    (hr29 : st.regs 29 = (activeVertsList G).headD 0)
    (hr30 : st.regs 30 = bPtr)
    (hr31 : st.regs 31 = bfsHeap)
    (hr32 : st.regs 32 = B.length)
    (hnl_at : ListAt st.mem heap (nonloopEdges G))
    (hinact_at : ListAt st.mem inactPtr (inactiveVertsList G.n (activeVertsList G)))
    (hB_at : ListAt st.mem bPtr B)
    (hvidx_at : ∀ u ∈ activeVertsList G, st.mem (newHeap + u) = (activeVertsList G).idxOf u)
    (hBr : ∀ v' : ℕ → ℝ, (∀ e < G.m, 0 < v' e) →
      IsBridgeVerts
        (MinCostFlow.LSF.weightedCopyGraph
          { G.toMGraph with E := (nonloopEdges G).toFinset } v')
        (activeVertsList G).toFinset ((activeVertsList G).headD 0) B)
    (hz_h3 : ZeroFrom st.mem (bfsHeap + 2 * G.n))
    (hpres : ∀ a < heap, st.mem a = mem_orig a)
    (tail : Stmt) (tailCost : ℕ) (Q_out : Outcome → State → Prop)
    (htail : ∀ (s12 : State) (simHeap hp_end k12 : ℕ),
      s12.regs 43 = simHeap →
      simHeap + 5 ≤ hp_end →
      s12.mem (simHeap + 1) = hp_end →
      heap ≤ hp_end →
      hp_end ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h →
      ZeroFrom s12.mem hp_end →
      LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) s12.mem →
      ZeroFrom s12.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) →
      k12 + tailCost ≤ T →
      ∃ o st' c, Runs w P ω tail s12 o st' c ∧ Q_out o st' ∧ k12 + c ≤ T)
    (hk : k + (weightsCost G.m L + (110 * G.m + (4 * G.m) * (70 * L_sim + 110) +
        50 * L_sim + 120) +
      simDecodeCost Q_AN (w'Max c_AN G.n G.m L h) (2 * G.m) (4 * G.m) G.n L_sim
        (anCostBound K_AN G.n G.m L_sim h) + (tailCost + 198)) ≤ T) :
    ∃ o st' c,
      Runs w P ω
        (.assign 33 (.bin .add (.reg 31) (.bin .mul (.const 2) (.reg 0))) ;;
         .assign 34 (.bin .add (.reg 33) (.reg 20)) ;;
         .assign 35 (.bin .add (.reg 34) (.const 1)) ;;
         .assign 36 (.bin .add (.reg 35) (.bin .mul (.reg 20) (.reg 7))) ;;
         .call 37 (lsstWeightsBase b + idxWeightsEntry)
           [.reg 20, .reg 11, .reg 4, .reg 5, .reg 23, .reg 6, .reg 33, .reg 35, .reg 34, .reg 36] ;;
         .assign 38 (.load (.reg 34)) ;;
         .assign 39 (.bin .add (.reg 37) (.bin .mul (.const 2) (.reg 20))) ;;
         .call 40 (lsstEncodeBase b + idxEncodeGAug)
           [.reg 20, .reg 11, .reg 2, .reg 3, .reg 22, .reg 33, .reg 35, .reg 38, .reg 23,
             .reg 32, .reg 30, .reg 7, .const (2 ^ h), .reg 37, .reg 39] ;;
         .assign 41 (.bin .add (.reg 40) (.reg 32)) ;;
         .assign 42 (.bin .add (.const 2) (.bin .mul (.const 3) (.reg 41))) ;;
         .assign 43 (.bin .add (.reg 39) (.bin .mul (.reg 42) (.reg 7))) ;;
         .call 45 (lsstEncodeBase b + idxSimDecode)
           [.reg 23, .reg 41, .reg 40, .reg 32, .reg 30, .reg 24, .reg 26, .reg 29, .reg 39,
             .reg 7, .const h, .const (2 ^ h), .reg 37, .reg 8, .reg 9, .reg 10, .reg 43] ;;
         tail)
        st o st' c ∧
      Q_out o st' ∧
      k + c ≤ T := by
  set nl := nonloopEdges G
  set V_list := activeVertsList G
  set inact := inactiveVertsList G.n V_list
  set h3 := bfsHeap + 2 * G.n
  set outMultPtr := h3
  set outKPtr := outMultPtr + nl.length
  set outWPtr := outKPtr + 1
  set wHeap := outWPtr + nl.length * L_sim
  have hw2 : 2 * h + 2 ≤ w := by omega
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hw0 : 0 < 2 ^ w := Nat.lt_trans Nat.zero_lt_one hw1
  have h2_w : 2 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have h3_w : 3 < 2 ^ w := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ w))
  have h2h_w : 2 ^ h < 2 ^ w :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) (by omega : h < w)) (le_refl _)
  have hh_w : h < 2 ^ w := lt_trans (Nat.lt_two_pow_self (n := h)) h2h_w
  have hnl_pos : 1 ≤ nl.length := Nat.pos_of_ne_zero hnl_ne
  have hnl_m : nl.length ≤ G.m := nonloopEdges_length_le G
  have hV_le : V_list.length ≤ G.n := activeVertsList_length_le G
  have hI_le : inact.length ≤ G.n := inactiveVertsList_length_le G.n V_list
  have hVI_le : V_list.length + inact.length ≤ G.n := active_add_inactive_le G
  have hV_ge2 : 2 ≤ V_list.length := activeVertsList_ge_two_of_nl hG hnl_ne
  obtain ⟨hK_m_le, hw'_lh_max, hlog_lh⟩ := lsstLSimMin_bounds hc_pos h1 hLsim
  set K := kWidthOf nl.length L
  have hK_pos : 1 ≤ K := le_trans (by decide : 1 ≤ 5) (kWidthOf_ge_five nl.length L hL1)
  have hK_le : K ≤ L_sim := le_trans (kWidthOf_mono hnl_m) hK_m_le
  have hL_le_Lsim : L ≤ L_sim := by
    have : L ≤ kWidthOf G.m L := by dsimp only [kWidthOf]; omega
    exact le_trans this hK_m_le
  have hh3_eq : h3 = heap + G.m + 3 + 9 * G.n + 2 * nl.length := by
    dsimp only [h3]
    rw [hbfsP, hbP, hnew]
    ring
  have hsp_h3 : h3 ≤ heap + (4 + 9 * G.n + 4 * G.m) := by
    rw [hh3_eq]
    linarith only [hnl_m]
  have hwHeap_eq : wHeap = h3 + nl.length + 1 + nl.length * L_sim := rfl
  have hh3_le_wHeap : h3 ≤ wHeap := by
    rw [hwHeap_eq]
    exact le_trans (Nat.le_add_right h3 nl.length)
      (le_trans (Nat.le_add_right (h3 + nl.length) 1) (Nat.le_add_right (h3 + nl.length + 1) _))
  have hwHeap_le : wHeap ≤ heap + (4 + 9 * G.n + 4 * G.m + G.m * L_sim) := by
    have hmul : nl.length * L_sim ≤ G.m * L_sim := Nat.mul_le_mul_right _ hnl_m
    rw [hwHeap_eq, hh3_eq]
    linarith only [hmul, hnl_m]
  -- Basic word bounds from lsstSpace
  have hLsim_le_sp : L_sim ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    have h1' : L_sim ≤ (2 + 3 * (4 * G.m)) * L_sim :=
      Nat.le_mul_of_pos_left L_sim (Nat.add_pos_left (by decide) _)
    have h2' : (2 + 3 * (4 * G.m)) * L_sim ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
      dsimp only [lsstSpace]
      exact le_trans (Nat.le_add_left ((2 + 3 * (4 * G.m)) * L_sim) _) (Nat.le_add_right _ _)
    exact le_trans h1' h2'
  have hheap_lt_w : heap < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hheap_space
  have hwHeap_sp : wHeap + weightsSpace nl.length K ≤
      heap + ((4 + 9 * G.n + 4 * G.m + G.m * L_sim) + weightsSpace G.m L_sim) := by
    have hws := weightsSpace_mono hnl_m hK_le
    linarith only [hwHeap_le, hws]
  have hwEnd_max_lt : heap + ((4 + 9 * G.n + 4 * G.m + G.m * L_sim) + weightsSpace G.m L_sim) < 2 ^ w := by
    have hle : (4 + 9 * G.n + 4 * G.m + G.m * L_sim) + weightsSpace G.m L_sim ≤
        lsstSpace Q_AN K_AN G.n G.m L_sim h := by
      dsimp only [lsstSpace]; omega
    linarith only [hheap_space, hle]
  have hwHeap_w : wHeap < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right _ _) (lt_of_le_of_lt hwHeap_sp hwEnd_max_lt)
  have houtMult_w : outMultPtr < 2 ^ w := lt_of_le_of_lt hh3_le_wHeap hwHeap_w
  have houtK_w : outKPtr < 2 ^ w := by
    have : outKPtr ≤ wHeap := by
      rw [hwHeap_eq]
      exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    exact lt_of_le_of_lt this hwHeap_w
  have houtW_w : outWPtr < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_right outWPtr (nl.length * L_sim)) hwHeap_w
  have h2n_w : 2 * G.n < 2 ^ w := by
    have h1' : 2 * G.n ≤ h3 := Nat.le_add_left _ _
    exact lt_of_le_of_lt (le_trans h1' hh3_le_wHeap) hwHeap_w
  have hnL_Lsim_w : nl.length * L_sim < 2 ^ w := by
    have : nl.length * L_sim ≤ wHeap := by rw [hwHeap_eq]; exact Nat.le_add_left _ _
    exact lt_of_le_of_lt this hwHeap_w
  have hLsim_w : L_sim < 2 ^ w :=
    lt_of_le_of_lt (le_trans hLsim_le_sp (Nat.le_add_left _ heap)) hheap_space
  have hK_w : K < 2 ^ w := lt_of_le_of_lt hK_le hLsim_w
  have hL_w : L < 2 ^ w := lt_of_le_of_lt hL_le_Lsim hLsim_w
  have hm_le_sp : G.m ≤ lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    dsimp only [lsstSpace]; omega
  have hm_w : G.m < 2 ^ w :=
    lt_of_le_of_lt (le_trans hm_le_sp (Nat.le_add_left _ heap)) hheap_space
  have hnl_w : nl.length < 2 ^ w := lt_of_le_of_lt hnl_m hm_w
  have hn_w : G.n < 2 ^ w := lt_of_le_of_lt (by linarith only) h2n_w
  have hV_w : V_list.length < 2 ^ w := lt_of_le_of_lt hV_le hn_w
  have hI_w : inact.length < 2 ^ w := lt_of_le_of_lt hI_le hn_w
  have hB_w : B.length < 2 ^ w := lt_of_le_of_lt (le_trans hB_le hV_le) hn_w
  have hbfsHeap_w : bfsHeap < 2 ^ w :=
    lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hh3_le_wHeap) hwHeap_w
  have hbPtr_w : bPtr < 2 ^ w := by rw [hbfsP] at hbfsHeap_w; linarith only [hbfsHeap_w]
  have hnewHeap_w : newHeap < 2 ^ w := by rw [hbP] at hbPtr_w; linarith only [hbPtr_w]
  have hinPtr_w : inactPtr < 2 ^ w := by
    have : inactPtr ≤ newHeap := by rw [hinP, hvL, hnew]; linarith only
    exact lt_of_le_of_lt this hnewHeap_w
  have hlenA_w : lenArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hlen_lt) hheap_lt_w
  have hwtA_w : wtArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hwt_lt) hheap_lt_w
  have htA_w : tailArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) ht_lt) hheap_lt_w
  have hhA_w : headArr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hh_lt) hheap_lt_w
  have hoo_w : outOrigPtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hoo_lt) hheap_lt_w
  have hob_w : outBridgePtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hob_lt) hheap_lt_w
  have hoh_w : outHdrPtr < 2 ^ w := lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hoh_lt) hheap_lt_w
  have hr₀_w : V_list.headD 0 < 2 ^ w := by
    have : V_list.headD 0 < G.n := by
      have h0 : 0 < V_list.length := by linarith only [hV_ge2]
      rw [headD_eq_getElem_zero V_list h0]
      exact (mem_activeVertsList_iff.mp (List.getElem_mem h0)).1
    exact lt_of_lt_of_le this (le_of_lt hn_w)
  -- Steps 14..17: assign 33..36
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hr31) (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq hrg.r0) h2n_w)
      (by dsimp only [outMultPtr, h3] at houtMult_w; exact houtMult_w))
    rfl fun s1 hm1 _ hr1 => ?_
  have hrg1 := lsstInRegs_upd hrg hr1 (by decide)
  have hs1_20 : s1.regs 20 = nl.length := by rw [hr1, Function.update_of_ne (by decide)]; exact hr20
  have hs1_22 : s1.regs 22 = newHeap := by rw [hr1, Function.update_of_ne (by decide)]; exact hr22
  have hs1_23 : s1.regs 23 = V_list.length := by rw [hr1, Function.update_of_ne (by decide)]; exact hr23
  have hs1_24 : s1.regs 24 = inact.length := by rw [hr1, Function.update_of_ne (by decide)]; exact hr24
  have hs1_26 : s1.regs 26 = inactPtr := by rw [hr1, Function.update_of_ne (by decide)]; exact hr26
  have hs1_29 : s1.regs 29 = V_list.headD 0 := by rw [hr1, Function.update_of_ne (by decide)]; exact hr29
  have hs1_30 : s1.regs 30 = bPtr := by rw [hr1, Function.update_of_ne (by decide)]; exact hr30
  have hs1_32 : s1.regs 32 = B.length := by rw [hr1, Function.update_of_ne (by decide)]; exact hr32
  have hs1_33 : s1.regs 33 = outMultPtr := by rw [hr1, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs1_33) (Expr.eval_reg_of_eq hs1_20) houtK_w)
    rfl fun s2 hm2 _ hr2 => ?_
  have hrg2 := lsstInRegs_upd hrg1 hr2 (by decide)
  have hs2_20 : s2.regs 20 = nl.length := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_20
  have hs2_22 : s2.regs 22 = newHeap := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_22
  have hs2_23 : s2.regs 23 = V_list.length := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_23
  have hs2_24 : s2.regs 24 = inact.length := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_24
  have hs2_26 : s2.regs 26 = inactPtr := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_26
  have hs2_29 : s2.regs 29 = V_list.headD 0 := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_29
  have hs2_30 : s2.regs 30 = bPtr := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_30
  have hs2_32 : s2.regs 32 = B.length := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_32
  have hs2_33 : s2.regs 33 = outMultPtr := by rw [hr2, Function.update_of_ne (by decide)]; exact hs1_33
  have hs2_34 : s2.regs 34 = outKPtr := by rw [hr2, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs2_34) (Expr.eval_const hw1) houtW_w)
    rfl fun s3 hm3 _ hr3 => ?_
  have hrg3 := lsstInRegs_upd hrg2 hr3 (by decide)
  have hs3_20 : s3.regs 20 = nl.length := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_20
  have hs3_22 : s3.regs 22 = newHeap := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_22
  have hs3_23 : s3.regs 23 = V_list.length := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_23
  have hs3_24 : s3.regs 24 = inact.length := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_24
  have hs3_26 : s3.regs 26 = inactPtr := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_26
  have hs3_29 : s3.regs 29 = V_list.headD 0 := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_29
  have hs3_30 : s3.regs 30 = bPtr := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_30
  have hs3_32 : s3.regs 32 = B.length := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_32
  have hs3_33 : s3.regs 33 = outMultPtr := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_33
  have hs3_34 : s3.regs 34 = outKPtr := by rw [hr3, Function.update_of_ne (by decide)]; exact hs2_34
  have hs3_35 : s3.regs 35 = outWPtr := by rw [hr3, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs3_35)
      (Expr.eval_mul (Expr.eval_reg_of_eq hs3_20) (Expr.eval_reg_of_eq hrg3.r7) hnL_Lsim_w) hwHeap_w)
    rfl fun s4 hm4 _ hr4 => ?_
  have hrg4 := lsstInRegs_upd hrg3 hr4 (by decide)
  have hs4_20 : s4.regs 20 = nl.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_20
  have hs4_22 : s4.regs 22 = newHeap := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_22
  have hs4_23 : s4.regs 23 = V_list.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_23
  have hs4_24 : s4.regs 24 = inact.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_24
  have hs4_26 : s4.regs 26 = inactPtr := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_26
  have hs4_29 : s4.regs 29 = V_list.headD 0 := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_29
  have hs4_30 : s4.regs 30 = bPtr := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_30
  have hs4_32 : s4.regs 32 = B.length := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_32
  have hs4_33 : s4.regs 33 = outMultPtr := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_33
  have hs4_34 : s4.regs 34 = outKPtr := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_34
  have hs4_35 : s4.regs 35 = outWPtr := by rw [hr4, Function.update_of_ne (by decide)]; exact hs3_35
  have hs4_36 : s4.regs 36 = wHeap := by rw [hr4, Function.update_self]
  have hs4_mem : s4.mem = st.mem := hm4.trans (hm3.trans (hm2.trans hm1))
  have hs4_len : ∀ e < G.m, Num.Valid s4.mem (lenArr + e * L) h L ∧
      Num.fixVal s4.mem (lenArr + e * L) h L P_fp = ℓ e ∧ 0 < ℓ e := fun e he => by
    have horig := hlen_orig e he
    have hm_eq : ∀ q < L, s4.mem (lenArr + e * L + q) = mem_orig (lenArr + e * L + q) := fun q hq => by
      have hmul : e * L + L ≤ G.m * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
        rwa [Nat.succ_mul] at this
      rw [hs4_mem, hpres _ (by linarith only [hq, hmul, hlen_lt])]
    have hcv := numValid_fixVal_congr (P_fp := P_fp) horig.1 hm_eq
    exact ⟨hcv.1, hcv.2.trans horig.2.1, horig.2.2⟩
  have hs4_wt : ∀ e < G.m, Num.Valid s4.mem (wtArr + e * L) h L ∧
      Num.fixVal s4.mem (wtArr + e * L) h L P_fp = v e ∧ 0 < v e := fun e he => by
    have horig := hwt_orig e he
    have hm_eq : ∀ q < L, s4.mem (wtArr + e * L + q) = mem_orig (wtArr + e * L + q) := fun q hq => by
      have hmul : e * L + L ≤ G.m * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
        rwa [Nat.succ_mul] at this
      rw [hs4_mem, hpres _ (by linarith only [hq, hmul, hwt_lt])]
    have hcv := numValid_fixVal_congr (P_fp := P_fp) horig.1 hm_eq
    exact ⟨hcv.1, hcv.2.trans horig.2.1, horig.2.2⟩
  -- Step 18: call weights
  have hheap_h3 : heap + nl.length ≤ h3 := by
    rw [hh3_eq]
    linarith only [hnl_m]
  have hheap_le_h3 : heap ≤ h3 := le_trans (Nat.le_add_right _ _) hheap_h3
  have houtW_end : outWPtr + nl.length * K ≤ wHeap := by
    have hmul := Nat.mul_le_mul_left nl.length hK_le
    dsimp only [wHeap]
    linarith only [hmul]
  have hw_gt_K : outWPtr ≤ wHeap := le_trans (Nat.le_add_right _ _) houtW_end
  have hom_lt_K : outMultPtr + nl.length ≤ outKPtr := by dsimp only [outKPtr]; linarith only
  have hoK_lt_W : outKPtr < outWPtr := by dsimp only [outWPtr]; linarith only
  have hheap_le_wHeap : heap ≤ wHeap := le_trans hheap_le_h3 hh3_le_wHeap
  have houtMult_end_wHeap : outMultPtr + nl.length ≤ wHeap := by
    have : outMultPtr + nl.length = outKPtr := rfl
    rw [this, hwHeap_eq]
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  obtain ⟨st_w, c_w, hrun_w, hm_K, hz_wEnd, hfr_w, hmw_ex, hc_w⟩ :=
    weights_runs (ω := ω) (pos := s4.pos) (lsst_hasAt_weights hp) G v ℓ heap lenArr wtArr L P_fp
      outMultPtr outWPtr outKPtr wHeap
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hG hL1 h1 hw hnl_pos (hs4_mem.symm ▸ hnl_at) hs4_len hs4_wt
      (le_trans hheap_h3 hh3_le_wHeap)
      (le_trans hlen_lt hheap_le_wHeap)
      (le_trans hwt_lt hheap_le_wHeap)
      houtMult_end_wHeap
      houtW_end
      (by linarith only [hoK_lt_W, hw_gt_K])
      (Or.inl (by linarith only [hom_lt_K, hoK_lt_W]))
      (Or.inl hom_lt_K)
      (Or.inr (by linarith only [hoK_lt_W]))
      (Or.inr hheap_h3)
      (Or.inr (le_trans hlen_lt hheap_le_h3))
      (Or.inr (le_trans hwt_lt hheap_le_h3))
      (Or.inr (by linarith only [hheap_h3, hom_lt_K, hoK_lt_W]))
      (Or.inr (le_trans hlen_lt (by linarith only [hheap_le_h3, hom_lt_K, hoK_lt_W])))
      (Or.inr (le_trans hwt_lt (by linarith only [hheap_le_h3, hom_lt_K, hoK_lt_W])))
      (Or.inr (by linarith only [hheap_h3, hom_lt_K]))
      (Or.inr (le_trans hlen_lt (by linarith only [hheap_le_h3, hom_lt_K])))
      (Or.inr (le_trans hwt_lt (by linarith only [hheap_le_h3, hom_lt_K])))
      (fun q hq => by rw [hs4_mem]; exact hz_h3 q (le_trans hh3_le_wHeap hq))
      (lt_of_le_of_lt hwHeap_sp hwEnd_max_lt)
  obtain ⟨mult, w_orig, δ, hmult_mem, hw_limbs, hmult_spec, hmult_rng, hδ_pos, hw_orig_rng, hℓ_up, hℓ_lo, hδ_Va⟩ := hmw_ex
  set wEnd := wHeap + weightsSpace nl.length K
  have hwEnd_le : wEnd ≤ heap + ((4 + 9 * G.n + 4 * G.m + G.m * L_sim) + weightsSpace G.m L_sim) := hwHeap_sp
  have hwEnd_w : wEnd < 2 ^ w := lt_of_le_of_lt hwHeap_sp hwEnd_max_lt
  have hc_w_m : c_w ≤ weightsCost G.m L := le_trans hc_w (weightsCost_mono hnl_m)
  refine runs_seq_call_runs_step (lsst_procs_weights hp)
    (evalArgs_cons (Expr.eval_reg_of_eq hs4_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hrg4.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg4.r4)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg4.r5)
            (evalArgs_cons (Expr.eval_reg_of_eq hs4_23)
              (evalArgs_cons (Expr.eval_reg_of_eq hrg4.r6)
                (evalArgs_cons (Expr.eval_reg_of_eq hs4_33)
                  (evalArgs_cons (Expr.eval_reg_of_eq hs4_35)
                    (evalArgs_cons (Expr.eval_reg_of_eq hs4_34)
                      (evalArgs_cons (Expr.eval_reg_of_eq hs4_36) (evalArgs_nil _ _)))))))))))
    hrun_w hc_w_m fun s5 hm5 hr5 => ?_
  have hrg5 := lsstInRegs_upd hrg4 hr5 (by decide)
  have hs5_20 : s5.regs 20 = nl.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_20
  have hs5_22 : s5.regs 22 = newHeap := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_22
  have hs5_23 : s5.regs 23 = V_list.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_23
  have hs5_24 : s5.regs 24 = inact.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_24
  have hs5_26 : s5.regs 26 = inactPtr := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_26
  have hs5_29 : s5.regs 29 = V_list.headD 0 := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_29
  have hs5_30 : s5.regs 30 = bPtr := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_30
  have hs5_32 : s5.regs 32 = B.length := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_32
  have hs5_33 : s5.regs 33 = outMultPtr := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_33
  have hs5_34 : s5.regs 34 = outKPtr := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_34
  have hs5_35 : s5.regs 35 = outWPtr := by rw [hr5, Function.update_of_ne (by decide)]; exact hs4_35
  have hs5_37 : s5.regs 37 = wEnd := by rw [hr5, Function.update_self]
  have hs5_pres_h3 : ∀ a < h3, s5.mem a = st.mem a := fun a ha => by
    have ha_w : a < wHeap := lt_of_lt_of_le ha hh3_le_wHeap
    have hom : a < outMultPtr ∨ outMultPtr + nl.length ≤ a := Or.inl ha
    have how : a < outWPtr ∨ outWPtr + nl.length * K ≤ a :=
      Or.inl (by dsimp only [outWPtr, outKPtr, outMultPtr]; linarith only [ha])
    have hoK : a ≠ outKPtr := ne_of_lt (by dsimp only [outKPtr, outMultPtr]; linarith only [ha])
    rw [hm5, hfr_w a ha_w hom how hoK, hs4_mem]
  -- Bounds for G_aug, [AN19], and encLen
  set m₁ := (nl.map mult).sum
  set m_aug := m₁ + B.length
  set encLen := 2 + 3 * m_aug
  set arrPtr := wEnd + 2 * nl.length
  set simHeap := arrPtr + encLen * L_sim
  let G_aug := buildGAug G V_list B mult w_orig
  have hV_2nl : V_list.length ≤ 2 * nl.length := activeVertsList_length_le_two_mul_nl G
  have hV_2m : V_list.length ≤ 2 * G.m := le_trans hV_2nl (Nat.mul_le_mul_left 2 hnl_m)
  have hv_nl : ∀ e ∈ nonloopEdges G, 0 < v e := fun e he =>
    (hwt_orig e (mem_nonloopEdges_iff.mp he).1).2.2
  have hm₁_2nl : m₁ ≤ 2 * nl.length := mult_sum_le_two_mul_nl hv_nl hmult_spec
  obtain ⟨hm₁_m2, hm_aug_le, hG_aug_enc_len, hw'_bound⟩ :=
    wordSize_bound_of_weights (c_AN := c_AN) hV_2nl hB_le hm₁_2nl
      (fun e he => (hw_orig_rng e he).2)
  have h2nl_2m : 2 * nl.length ≤ 2 * G.m := Nat.mul_le_mul_left 2 hnl_m
  have harr_le : arrPtr ≤ heap + ((4 + 9 * G.n + 4 * G.m + G.m * L_sim) + weightsSpace G.m L_sim + 2 * G.m) := by
    dsimp only [arrPtr]
    linarith only [hwEnd_le, h2nl_2m]
  have hencL_le : encLen * L_sim ≤ (2 + 3 * (4 * G.m)) * L_sim :=
    Nat.mul_le_mul_right L_sim (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm_aug_le) 2)
  have hsimHeap_sp : simHeap + simDecodeSpace Q_AN (2 * G.m) (4 * G.m) L_sim h (anCostBound K_AN G.n G.m L_sim h) ≤
      heap + lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    dsimp only [simHeap, lsstSpace]
    linarith only [harr_le, hencL_le]
  have hsimHeap_lt_sp : simHeap < heap + lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    have hpos : 0 < simDecodeSpace Q_AN (2 * G.m) (4 * G.m) L_sim h (anCostBound K_AN G.n G.m L_sim h) := by
      dsimp only [simDecodeSpace]
      exact Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left (Nat.add_pos_left (by decide) _) _) _) _
    exact lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) hsimHeap_sp
  have hsimHeap_w : simHeap < 2 ^ w := lt_trans hsimHeap_lt_sp hheap_space
  have harr_w : arrPtr < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hsimHeap_w
  have h2nl_w : 2 * nl.length < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_add_left _ wEnd) harr_w
  have hencL_w : encLen * L_sim < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ arrPtr) hsimHeap_w
  have hencLen_w : encLen < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by linarith only [hK_pos, hK_le])) hencL_w
  have h3m_w : 3 * m_aug < 2 ^ w :=
    lt_of_le_of_lt (by change 3 * m_aug ≤ 2 + 3 * m_aug; exact Nat.le_add_left _ _) hencLen_w
  have hm_aug_w : m_aug < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left m_aug (by decide : 0 < 3)) h3m_w
  have hm₁_w : m₁ < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right m₁ B.length) hm_aug_w
  have hpow2_lh : 6 + 16 * G.m < 2 ^ (L_sim * h) :=
    lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
      (Nat.pow_le_pow_right (by norm_num) hlog_lh)
  have hV_pos : 0 < V_list.length := lt_of_lt_of_le (by decide) hV_ge2
  have hV_lt_lh : V_list.length < 2 ^ (L_sim * h) :=
    lt_of_le_of_lt hV_2m (lt_trans (by linarith only : 2 * G.m < 6 + 16 * G.m) hpow2_lh)
  have hV_fit : V_list.length - 1 ≤ 2 ^ (L_sim * h) := le_trans (Nat.sub_le _ _) hV_lt_lh.le
  have hm_fit : 2 + 3 * (m₁ + B.length) ≤ 2 ^ (L_sim * h) :=
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm_aug_le) 2)
      (le_trans (by linarith only : 2 + 3 * (4 * G.m) ≤ 6 + 16 * G.m) hpow2_lh.le)
  have hmB_lt_lh : m₁ + B.length < 2 ^ (L_sim * h) :=
    lt_of_le_of_lt (le_trans hm_aug_le (by linarith only : 4 * G.m ≤ 6 + 16 * G.m)) hpow2_lh
  -- Apply `[AN19]` on `G_aug`
  set w' := WordRAM.wordSize c_AN G_aug.encode
  obtain ⟨hw'1, hx_lt⟩ := wordSize_one_le hc_pos G_aug.encode
  have hw'_lh : w' ≤ L_sim * h := le_trans hw'_bound hw'_lh_max
  have hnl_ne_fin : (nonloopEdges G).toFinset.Nonempty := by
    have h0 : 0 < nl.length := hnl_pos
    exact ⟨nl[0]'h0, List.mem_toFinset.mpr (List.getElem_mem h0)⟩
  have hV_mem_iff : ∀ x, x ∈ V_list ↔ x ∈ activeVertsList G := fun _ => Iff.rfl
  have hV_act_iff : ∀ x, x ∈ activeVertsList G ↔ x ∈ V_list.toFinset := fun x => List.mem_toFinset.symm
  have hv_all_pos : ∀ e < G.m, 0 < v e := fun e he => (hwt_orig e he).2.2
  have hB_spec : IsBridgeVerts (MinCostFlow.LSF.weightedCopyGraph { G.toMGraph with E := (nonloopEdges G).toFinset } v)
      V_list.toFinset (V_list.headD 0) B := hBr v hv_all_pos
  have hGAug_val : G_aug.graph.IsValid :=
    buildGAug_graph_isValid hG hnl_ne_fin hV_mem_iff hV_act_iff hB_spec
  have hGAug_ll : G_aug.graph.IsLoopless :=
    buildGAug_graph_isLoopless hG hnl_ne_fin (activeVertsList_nodup G) hV_mem_iff hV_act_iff hB_spec
  have hGAug_conn : G_aug.IsConnected :=
    buildGAug_isConnected hG rfl rfl hnl_ne_fin (activeVertsList_nodup G) hV_mem_iff hV_act_iff hB_spec
      (fun e he => (hmult_rng e he).1)
  have hGAug_wpos : ∀ e ∈ G_aug.edges, 1 ≤ e.2.2 :=
    buildGAug_weight_ge_one (fun e he => le_trans (by decide : 1 ≤ 4) (hw_orig_rng e he).1)
  obtain ⟨out, cost, hrun_AN, hout_st, htot_st, hcost_AN⟩ :=
    hAN G_aug hGAug_val hGAug_ll hGAug_conn hGAug_wpos
  have hmaxW_le : G_aug.maxWeight ≤ 2 ^ (L_sim * h) := by
    refine buildGAug_maxWeight_le (Nat.one_le_pow _ 2 (by norm_num)) fun e he => ?_
    have hlt := (hw_orig_rng e he).2
    have hexp : K * h - 1 ≤ L_sim * h := le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right h hK_le)
    exact le_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hexp))
  have hGAug_m : G_aug.m = m_aug := by
    rw [buildGAug_m, copyEdgeList_length]
  have hcost_bound : cost ≤ anCostBound K_AN G.n G.m L_sim h := by
    rw [buildGAug_n, hGAug_m] at hcost_AN
    exact anCost_le_bound hV_ge2 hV_le hm_aug_le hmaxW_le hcost_AN
  have hsim_sp_total : simHeap + simDecodeSpace Q_AN V_list.length m_aug L_sim h cost < 2 ^ w := by
    have hsd := simDecodeSpace_mono (Q := Q_AN) (L_sim := L_sim) (h := h) hV_2m hm_aug_le hcost_bound
    exact lt_of_le_of_lt (Nat.add_le_add_left hsd _) (lt_of_le_of_lt hsimHeap_sp hheap_space)
  -- Steps 19..20: assign 38 (K), assign 39 (arrPtr)
  refine runs_seq_assign_step
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq hs5_34) (hm5 ▸ hm_K))
    rfl fun s6 hm6 _ hr6 => ?_
  have hrg6 := lsstInRegs_upd hrg5 hr6 (by decide)
  have hs6_20 : s6.regs 20 = nl.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_20
  have hs6_22 : s6.regs 22 = newHeap := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_22
  have hs6_23 : s6.regs 23 = V_list.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_23
  have hs6_24 : s6.regs 24 = inact.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_24
  have hs6_26 : s6.regs 26 = inactPtr := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_26
  have hs6_29 : s6.regs 29 = V_list.headD 0 := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_29
  have hs6_30 : s6.regs 30 = bPtr := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_30
  have hs6_32 : s6.regs 32 = B.length := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_32
  have hs6_33 : s6.regs 33 = outMultPtr := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_33
  have hs6_35 : s6.regs 35 = outWPtr := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_35
  have hs6_37 : s6.regs 37 = wEnd := by rw [hr6, Function.update_of_ne (by decide)]; exact hs5_37
  have hs6_38 : s6.regs 38 = K := by rw [hr6, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs6_37) (Expr.eval_mul (Expr.eval_const h2_w) (Expr.eval_reg_of_eq hs6_20) h2nl_w) harr_w)
    rfl fun s7 hm7 _ hr7 => ?_
  have hrg7 := lsstInRegs_upd hrg6 hr7 (by decide)
  have hs7_20 : s7.regs 20 = nl.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_20
  have hs7_22 : s7.regs 22 = newHeap := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_22
  have hs7_23 : s7.regs 23 = V_list.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_23
  have hs7_24 : s7.regs 24 = inact.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_24
  have hs7_26 : s7.regs 26 = inactPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_26
  have hs7_29 : s7.regs 29 = V_list.headD 0 := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_29
  have hs7_30 : s7.regs 30 = bPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_30
  have hs7_32 : s7.regs 32 = B.length := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_32
  have hs7_33 : s7.regs 33 = outMultPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_33
  have hs7_35 : s7.regs 35 = outWPtr := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_35
  have hs7_37 : s7.regs 37 = wEnd := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_37
  have hs7_38 : s7.regs 38 = K := by rw [hr7, Function.update_of_ne (by decide)]; exact hs6_38
  have hs7_39 : s7.regs 39 = arrPtr := by rw [hr7, Function.update_self]
  have hs7_mem : s7.mem = s5.mem := hm7.trans hm6
  have hB_mem_V : ∀ b ∈ B, b ∈ V_list := fun b hb => List.mem_toFinset.mp (hB_spec.2.1 b hb)
  have hV_sub_n : ∀ u ∈ V_list, u < G.n := fun u hu => (mem_activeVertsList_iff.mp hu).1
  have hbPtr_h3 : bPtr + B.length ≤ h3 := by
    have : B.length ≤ G.n := le_trans hB_le hV_le
    dsimp only [h3]
    rw [hbfsP]
    linarith only [this]
  have hinact_h3 : inactPtr + inact.length ≤ h3 := by
    dsimp only [h3]
    rw [hbfsP, hbP, hinP, hvL, hnew]
    linarith only [hI_le]
  -- Step 21: call encodeGAug
  have hwEnd_ge_wHeap : wHeap ≤ wEnd := Nat.le_add_right _ _
  have hwHeap_ge_outW : outWPtr + nl.length * K ≤ wHeap := houtW_end
  have hnew_h3 : newHeap + G.n ≤ h3 := by dsimp only [h3]; rw [hbfsP, hbP]; linarith only
  have hh3_wEnd : h3 ≤ wEnd := le_trans hh3_le_wHeap hwEnd_ge_wHeap
  have hheap_wEnd : heap ≤ wEnd := le_trans hheap_le_h3 hh3_wEnd
  have harr_ge_wEnd : wEnd ≤ arrPtr := Nat.le_add_right _ _
  obtain ⟨st_enc, c_enc, hrun_enc, horig_enc, henc_limbs, hfr_enc, hc_enc⟩ :=
    encodeGAug_runs (mem := s7.mem) (ω := ω) (pos₀ := s7.pos) (lsst_hasAt_encode hp) (lsst_hasAt_arith hp)
      G V_list B mult w_orig heap tailArr headArr newHeap outMultPtr outWPtr K bPtr L_sim wEnd arrPtr
      (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
      hG (activeVertsList_nodup G) hV_sub_n (fun _ he => nonloop_ends_mem_active hG he) hB_mem_V
      h1 hw2 hK_pos hK_le hV_lt_lh hmB_lt_lh hm_aug_w
      (lt_of_le_of_lt hheap_h3 (lt_of_le_of_lt hh3_wEnd hwEnd_w))
      (lt_of_le_of_lt ht_lt hheap_lt_w)
      (lt_of_le_of_lt hh_lt hheap_lt_w)
      (lt_of_le_of_lt hnew_h3 (lt_of_le_of_lt hh3_wEnd hwEnd_w))
      (lt_of_le_of_lt (by linarith only [hom_lt_K, hoK_lt_W, hw_gt_K]) hwHeap_w)
      (lt_of_le_of_lt houtW_end hwHeap_w)
      (lt_of_le_of_lt hbPtr_h3 (lt_of_le_of_lt hh3_wEnd hwEnd_w))
      (lt_of_le_of_lt (Nat.add_le_add_left hm₁_2nl wEnd) harr_w)
      hsimHeap_w
      (Or.inr (le_trans hheap_h3 (le_trans hh3_wEnd harr_ge_wEnd)))
      (Or.inr (le_trans ht_lt (le_trans hheap_wEnd harr_ge_wEnd)))
      (Or.inr (le_trans hh_lt (le_trans hheap_wEnd harr_ge_wEnd)))
      (Or.inr (le_trans hnew_h3 (le_trans hh3_wEnd harr_ge_wEnd)))
      (Or.inr (le_trans (le_trans hom_lt_K (le_trans (Nat.le_of_lt hoK_lt_W) (le_trans hw_gt_K hwEnd_ge_wHeap))) harr_ge_wEnd))
      (Or.inr (le_trans houtW_end (le_trans hwEnd_ge_wHeap harr_ge_wEnd)))
      (Or.inr (le_trans hbPtr_h3 (le_trans hh3_wEnd harr_ge_wEnd)))
      (Or.inl (Nat.add_le_add_left hm₁_2nl wEnd))
      (Or.inr (le_trans hheap_h3 hh3_wEnd))
      (Or.inr (le_trans ht_lt hheap_wEnd))
      (Or.inr (le_trans hh_lt hheap_wEnd))
      (Or.inr (le_trans hnew_h3 hh3_wEnd))
      (Or.inr (le_trans hom_lt_K (le_trans (Nat.le_of_lt hoK_lt_W) (le_trans hw_gt_K hwEnd_ge_wHeap))))
      (Or.inr (le_trans houtW_end hwEnd_ge_wHeap))
      (Or.inr (le_trans hbPtr_h3 hh3_wEnd))
      (hnl_at.congr fun q hq1 hq2 => by rw [hs7_mem, hs5_pres_h3 q (lt_of_lt_of_le hq2 hheap_h3)])
      (htail_orig.congr fun q hq1 hq2 => by
        rw [List.length_ofFn] at hq2
        have hq_hp : q < heap := lt_of_lt_of_le hq2 ht_lt
        rw [hs7_mem, hs5_pres_h3 q (lt_of_lt_of_le hq_hp hheap_le_h3), hpres q hq_hp])
      (hhead_orig.congr fun q hq1 hq2 => by
        rw [List.length_ofFn] at hq2
        have hq_hp : q < heap := lt_of_lt_of_le hq2 hh_lt
        rw [hs7_mem, hs5_pres_h3 q (lt_of_lt_of_le hq_hp hheap_le_h3), hpres q hq_hp])
      (fun u hu => by
        have hlt : newHeap + u < h3 := lt_of_lt_of_le (Nat.add_lt_add_left (hV_sub_n u hu) newHeap) hnew_h3
        rw [hs7_mem, hs5_pres_h3 _ hlt]
        exact hvidx_at u hu)
      (fun j hj => by rw [hs7_mem, hm5]; exact hmult_mem j hj)
      (fun j hj => (hw_limbs j hj).congr fun q hq1 hq2 => by rw [hs7_mem, hm5])
      (hB_at.congr fun q hq1 hq2 => by rw [hs7_mem, hs5_pres_h3 q (lt_of_lt_of_le hq2 hbPtr_h3)])
  have hc_enc_bd : c_enc ≤ 110 * G.m + (4 * G.m) * (70 * L_sim + 110) + 50 * L_sim + 120 := by
    have hm₁_cost : ((List.range nl.length).map fun j => s7.mem (outMultPtr + j)).sum = m₁ := by
      have hmap_eq : (List.range nl.length).map (fun j => s7.mem (outMultPtr + j)) = nl.map mult := by
        refine List.ext_getElem (by simp) fun j hj1 hj2 => ?_
        simp only [List.getElem_map, List.getElem_range]
        rw [hs7_mem, hm5]
        exact hmult_mem j (by simpa using hj1)
      dsimp only [m₁]
      rw [hmap_eq]
    dsimp only [encodeGAugCost] at hc_enc
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some] at hc_enc
    rw [hm₁_cost] at hc_enc
    have hmul_m : m_aug * (70 * L_sim + 110) ≤ (4 * G.m) * (70 * L_sim + 110) :=
      Nat.mul_le_mul_right _ hm_aug_le
    have h110 : 110 * nl.length ≤ 110 * G.m := Nat.mul_le_mul_left 110 hnl_m
    change c_enc ≤ 110 * nl.length + m_aug * (70 * L_sim + 110) + 50 * L_sim + 120 at hc_enc
    exact le_trans hc_enc
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add h110 hmul_m) _) _)
  refine runs_seq_call_runs_step (lsst_procs_encodeGAug hp)
    (evalArgs_cons (Expr.eval_reg_of_eq hs7_20)
      (evalArgs_cons (Expr.eval_reg_of_eq hrg7.r11)
        (evalArgs_cons (Expr.eval_reg_of_eq hrg7.r2)
          (evalArgs_cons (Expr.eval_reg_of_eq hrg7.r3)
            (evalArgs_cons (Expr.eval_reg_of_eq hs7_22)
              (evalArgs_cons (Expr.eval_reg_of_eq hs7_33)
                (evalArgs_cons (Expr.eval_reg_of_eq hs7_35)
                  (evalArgs_cons (Expr.eval_reg_of_eq hs7_38)
                    (evalArgs_cons (Expr.eval_reg_of_eq hs7_23)
                      (evalArgs_cons (Expr.eval_reg_of_eq hs7_32)
                        (evalArgs_cons (Expr.eval_reg_of_eq hs7_30)
                          (evalArgs_cons (Expr.eval_reg_of_eq hrg7.r7)
                            (evalArgs_cons (Expr.eval_const h2h_w)
                              (evalArgs_cons (Expr.eval_reg_of_eq hs7_37)
                                (evalArgs_cons (Expr.eval_reg_of_eq hs7_39) (evalArgs_nil _ _))))))))))))))))
    hrun_enc hc_enc_bd fun s8 hm8 hr8 => ?_
  have hrg8 := lsstInRegs_upd hrg7 hr8 (by decide)
  have hs8_23 : s8.regs 23 = V_list.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_23
  have hs8_24 : s8.regs 24 = inact.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_24
  have hs8_26 : s8.regs 26 = inactPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_26
  have hs8_29 : s8.regs 29 = V_list.headD 0 := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_29
  have hs8_30 : s8.regs 30 = bPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_30
  have hs8_32 : s8.regs 32 = B.length := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_32
  have hs8_37 : s8.regs 37 = wEnd := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_37
  have hs8_39 : s8.regs 39 = arrPtr := by rw [hr8, Function.update_of_ne (by decide)]; exact hs7_39
  have hs8_40 : s8.regs 40 = m₁ := by rw [hr8, Function.update_self]
  -- Steps 22..24: assign 41 (m_aug), 42 (encLen), 43 (simHeap)
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs8_40) (Expr.eval_reg_of_eq hs8_32) hm_aug_w)
    rfl fun s9 hm9 _ hr9 => ?_
  have hrg9 := lsstInRegs_upd hrg8 hr9 (by decide)
  have hs9_23 : s9.regs 23 = V_list.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_23
  have hs9_24 : s9.regs 24 = inact.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_24
  have hs9_26 : s9.regs 26 = inactPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_26
  have hs9_29 : s9.regs 29 = V_list.headD 0 := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_29
  have hs9_30 : s9.regs 30 = bPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_30
  have hs9_32 : s9.regs 32 = B.length := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_32
  have hs9_37 : s9.regs 37 = wEnd := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_37
  have hs9_39 : s9.regs 39 = arrPtr := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_39
  have hs9_40 : s9.regs 40 = m₁ := by rw [hr9, Function.update_of_ne (by decide)]; exact hs8_40
  have hs9_41 : s9.regs 41 = m_aug := by rw [hr9, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_const h2_w) (Expr.eval_mul (Expr.eval_const h3_w) (Expr.eval_reg_of_eq hs9_41) h3m_w) hencLen_w)
    rfl fun s10 hm10 _ hr10 => ?_
  have hrg10 := lsstInRegs_upd hrg9 hr10 (by decide)
  have hs10_23 : s10.regs 23 = V_list.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_23
  have hs10_24 : s10.regs 24 = inact.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_24
  have hs10_26 : s10.regs 26 = inactPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_26
  have hs10_29 : s10.regs 29 = V_list.headD 0 := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_29
  have hs10_30 : s10.regs 30 = bPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_30
  have hs10_32 : s10.regs 32 = B.length := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_32
  have hs10_37 : s10.regs 37 = wEnd := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_37
  have hs10_39 : s10.regs 39 = arrPtr := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_39
  have hs10_40 : s10.regs 40 = m₁ := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_40
  have hs10_41 : s10.regs 41 = m_aug := by rw [hr10, Function.update_of_ne (by decide)]; exact hs9_41
  have hs10_42 : s10.regs 42 = encLen := by rw [hr10, Function.update_self]
  refine runs_seq_assign_step
    (Expr.eval_add (Expr.eval_reg_of_eq hs10_39) (Expr.eval_mul (Expr.eval_reg_of_eq hs10_42) (Expr.eval_reg_of_eq hrg10.r7) hencL_w) hsimHeap_w)
    rfl fun s11 hm11 _ hr11 => ?_
  have hrg11 := lsstInRegs_upd hrg10 hr11 (by decide)
  have hs11_23 : s11.regs 23 = V_list.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_23
  have hs11_24 : s11.regs 24 = inact.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_24
  have hs11_26 : s11.regs 26 = inactPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_26
  have hs11_29 : s11.regs 29 = V_list.headD 0 := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_29
  have hs11_30 : s11.regs 30 = bPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_30
  have hs11_32 : s11.regs 32 = B.length := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_32
  have hs11_37 : s11.regs 37 = wEnd := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_37
  have hs11_39 : s11.regs 39 = arrPtr := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_39
  have hs11_40 : s11.regs 40 = m₁ := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_40
  have hs11_41 : s11.regs 41 = m_aug := by rw [hr11, Function.update_of_ne (by decide)]; exact hs10_41
  have hs11_43 : s11.regs 43 = simHeap := by rw [hr11, Function.update_self]
  have hs11_mem : s11.mem = st_enc.mem := hm11.trans (hm10.trans (hm9.trans hm8))
  have hs11_lt_wEnd : ∀ a < wEnd, s11.mem a = s7.mem a := fun a ha => by
    have ha_arr : a < arrPtr := lt_of_lt_of_le ha (Nat.le_add_right _ _)
    rw [hs11_mem, hfr_enc a (Or.inl ha_arr) (Or.inl ha)]
  have hs11_lt_h3 : ∀ a < h3, s11.mem a = st.mem a := fun a ha => by
    rw [hs11_lt_wEnd a (lt_of_lt_of_le ha hh3_wEnd), hs7_mem, hs5_pres_h3 a ha]
  have hz_s11 : ZeroFrom s11.mem simHeap := fun a ha => by
    have ha_orig : wEnd + m₁ ≤ a := by
      have : wEnd + m₁ ≤ arrPtr := by dsimp only [arrPtr]; exact Nat.add_le_add_left hm₁_2nl _
      exact le_trans this (le_trans (Nat.le_add_right _ _) ha)
    have ha_wEnd : wEnd ≤ a := le_trans (Nat.le_add_right _ _) ha_orig
    rw [hs11_mem, hfr_enc a (Or.inr ha) (Or.inr ha_orig), hs7_mem, hm5]
    exact hz_wEnd a ha_wEnd
  have hout_len : out.length = V_list.length - 1 := by
    simpa [G_aug, buildGAug_n] using hout_st.2.2.1
  have hout_lt_w : ∀ x ∈ out, x < 2 ^ w := fun x hx => by
    have hx_m : x < G_aug.m := hout_st.2.1 x hx
    rw [hGAug_m] at hx_m
    exact lt_trans hx_m hm_aug_w
  -- Step 25: call simDecode
  have hsim_ge_arr : arrPtr ≤ simHeap := Nat.le_add_right _ _
  have hwEnd_sim : wEnd + m₁ ≤ simHeap :=
    le_trans (Nat.add_le_add_left hm₁_2nl wEnd) hsim_ge_arr
  have hheap_sim : heap ≤ simHeap := le_trans hheap_wEnd (le_trans harr_ge_wEnd hsim_ge_arr)
  have hbp_sim : bPtr + B.length ≤ simHeap := le_trans hbPtr_h3 (le_trans hh3_wEnd (le_trans harr_ge_wEnd hsim_ge_arr))
  have hin_sim : inactPtr + inact.length ≤ simHeap := le_trans hinact_h3 (le_trans hh3_wEnd (le_trans harr_ge_wEnd hsim_ge_arr))
  have hheap_bp : heap ≤ bPtr := by rw [hbP, hnew]; linarith only
  have hheap_in : heap ≤ inactPtr := by rw [hinP, hvL]; linarith only
  have hVm1_le : V_list.length - 1 ≤ G.n := le_trans (Nat.sub_le _ _) hV_le
  have hob_V_le : 2 * (V_list.length - 1 + inact.length) ≤ 2 * G.n :=
    Nat.mul_le_mul_left 2 (le_trans (Nat.add_le_add_right (Nat.sub_le _ _) _) hVI_le)
  have hoo_V_lt : outOrigPtr + (V_list.length - 1) ≤ heap :=
    le_trans (Nat.add_le_add_left hVm1_le outOrigPtr) hoo_lt
  have hob_V_lt : outBridgePtr + 2 * (V_list.length - 1 + inact.length) ≤ heap :=
    le_trans (Nat.add_le_add_left hob_V_le outBridgePtr) hob_lt
  obtain ⟨st_sim, c_sim, hrun_sim, hhdr0_s, hhdr1_s, hlo_s, hbr_s, hfr_s, hz_sim,
      ⟨hsim_c1_lo, hsim_c1_le, hsim_hz_c1⟩, hc_sim⟩ :=
    simDecode_runs (ω := ω) (pos₀ := s11.pos)
      (lsst_hasAt_sim hp) (lsst_hasAt_wrap hp) (lsst_hasAt_encode hp) (lsst_hasAt_pack hp)
      G V_list B mult w_orig bPtr inactPtr arrPtr L_sim wEnd outOrigPtr outBridgePtr outHdrPtr simHeap
      out cost h1 hw2 (le_trans hK_pos hK_le) hw'1 hw'_lh hV_pos hV_fit hm_fit hx_lt hout_len hout_lt_w hrun_AN
      hsim_sp_total hz_s11 (le_refl _) hbp_sim hin_sim hwEnd_sim
      (le_trans hoo_V_lt hheap_sim)
      (le_trans hob_V_lt hheap_sim)
      (le_trans hoh_lt hheap_sim)
      (disjointRanges_mono hd_ob hVm1_le hob_V_le)
      (disjointRanges_mono hd_oh hVm1_le le_rfl)
      (disjointRanges_mono hd_bh hob_V_le le_rfl)
      (Or.inl (le_trans hoo_V_lt hheap_wEnd))
      (Or.inl (le_trans hoo_V_lt hheap_bp))
      (Or.inl (le_trans hoo_V_lt hheap_in))
      (Or.inl (le_trans hob_V_lt hheap_wEnd))
      (Or.inl (le_trans hob_V_lt hheap_bp))
      (Or.inl (le_trans hob_V_lt hheap_in))
      (Or.inl (le_trans hoh_lt hheap_wEnd))
      (Or.inl (le_trans hoh_lt hheap_bp))
      (Or.inl (le_trans hoh_lt hheap_in))
      hr₀_w
      (fun x hx => by
        dsimp only [origOfCopy] at hx
        rw [List.mem_flatMap] at hx
        obtain ⟨e, he, hrep⟩ := hx
        rw [List.mem_replicate] at hrep
        rw [hrep.2]
        exact lt_trans (mem_nonloopEdges_iff.mp he).1 hm_w)
      (fun b hb => lt_trans (hV_sub_n b (hB_mem_V b hb)) hn_w)
      (fun x hx => lt_trans (mem_inactiveVertsList_lt hx) hn_w)
      (fun i hi => by
        refine (henc_limbs i hi).congr fun q hq1 hq2 => ?_
        rw [hs11_mem])
      (horig_enc.congr fun q hq1 hq2 => by rw [hs11_mem])
      (hB_at.congr fun q hq1 hq2 => by rw [hs11_lt_h3 q (lt_of_lt_of_le hq2 hbPtr_h3)])
      (hinact_at.congr fun q hq1 hq2 => by rw [hs11_lt_h3 q (lt_of_lt_of_le hq2 hinact_h3)])
  have hc_sim_bd : c_sim ≤ simDecodeCost Q_AN (w'Max c_AN G.n G.m L h) (2 * G.m) (4 * G.m) G.n L_sim
      (anCostBound K_AN G.n G.m L_sim h) :=
    le_trans hc_sim (simDecodeCost_mono hw'_bound hV_2m hm_aug_le hI_le hcost_bound)
  refine runs_seq_call_runs_step (lsst_procs_simDecode hp)
    (evalArgs_cons (Expr.eval_reg_of_eq hs11_23)
      (evalArgs_cons (Expr.eval_reg_of_eq hs11_41)
        (evalArgs_cons (Expr.eval_reg_of_eq hs11_40)
          (evalArgs_cons (Expr.eval_reg_of_eq hs11_32)
            (evalArgs_cons (Expr.eval_reg_of_eq hs11_30)
              (evalArgs_cons (Expr.eval_reg_of_eq hs11_24)
                (evalArgs_cons (Expr.eval_reg_of_eq hs11_26)
                  (evalArgs_cons (Expr.eval_reg_of_eq hs11_29)
                    (evalArgs_cons (Expr.eval_reg_of_eq hs11_39)
                      (evalArgs_cons (Expr.eval_reg_of_eq hrg11.r7)
                        (evalArgs_cons (Expr.eval_const hh_w)
                          (evalArgs_cons (Expr.eval_const h2h_w)
                            (evalArgs_cons (Expr.eval_reg_of_eq hs11_37)
                              (evalArgs_cons (Expr.eval_reg_of_eq hrg11.r8)
                                (evalArgs_cons (Expr.eval_reg_of_eq hrg11.r9)
                                  (evalArgs_cons (Expr.eval_reg_of_eq hrg11.r10)
                                    (evalArgs_cons (Expr.eval_reg_of_eq hs11_43) (evalArgs_nil _ _))))))))))))))))))
    hrun_sim hc_sim_bd fun s12 hm12 hr12 => ?_
  -- Step 26: ret 0 and verify LSST output
  set dec := decodeAN19Output G V_list B mult out
  have hdec1_len : dec.1.length ≤ G.n := by
    dsimp only [dec, decodeAN19Output]
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) (by rw [hout_len]; exact le_trans (Nat.sub_le _ _) hV_le)
  have hdec2_len : dec.2.length ≤ G.n := by
    dsimp only [dec, decodeAN19Output]
    rw [List.length_append, List.length_map, List.length_map]
    have h1 := List.length_filter_le (fun j => decide (m₁ ≤ j ∧ j < m₁ + B.length)) out
    rw [hout_len] at h1
    exact le_trans (Nat.add_le_add h1 le_rfl) (le_trans (Nat.add_le_add_right (Nat.sub_le _ _) _) hVI_le)
  have hlsst : MinCostFlow.LSF.IsLSST G.toMGraph ℓ v
      ((4 * max K_AN 1 + 5) * Real.log (↑G.n + 2) ^ 2)
      (decodedTree G.n G.m G.tail G.head dec.1 dec.2) := by
    have hℓ_pos : ∀ e ∈ G.toMGraph.E, 0 < ℓ e := fun e he => (hlen_orig e (Finset.mem_range.mp he)).2.2
    have hv_pos : ∀ e ∈ G.toMGraph.E, 0 < v e := fun e he => (hwt_orig e (Finset.mem_range.mp he)).2.2
    have hraw := concreteLSST_isLSST hG hnl_ne_fin hℓ_pos hv_pos (activeVertsList_nodup G) hV_mem_iff
      hV_act_iff hB_spec hmult_spec hδ_pos (fun e he => (hw_orig_rng e he).1) hℓ_up hℓ_lo
      (fun e he => by
        have hcard : V_list.toFinset.card = V_list.length := List.toFinset_card_of_nodup (activeVertsList_nodup G)
        rw [hcard]; exact hδ_Va e he)
      hout_st htot_st (le_max_right K_AN 1) (le_max_left K_AN 1)
    have heq_tree : concreteLSSTTree G V_list B mult out = decodedTree G.n G.m G.tail G.head dec.1 dec.2 := by
      dsimp only [concreteLSSTTree, dec]
      have hemp : (nonloopEdges G).isEmpty = false := by
        cases hlist : nonloopEdges G with
        | nil => exfalso; apply hnl_ne; simp [nl, hlist]
        | cons _ _ => rfl
      rw [hemp]; rfl
    rwa [← heq_tree]
  have hs12_frame : ∀ a < heap,
      (a < outOrigPtr ∨ outOrigPtr + G.n ≤ a) →
      (a < outBridgePtr ∨ outBridgePtr + 2 * G.n ≤ a) →
      (a < outHdrPtr ∨ outHdrPtr + 2 ≤ a) → s12.mem a = mem_orig a := by
    intro a ha hao hab hah
    have ha_sim : a < simHeap := lt_of_lt_of_le ha hheap_sim
    have ha_h3 : a < h3 := lt_of_lt_of_le ha hheap_le_h3
    have hao' : a < outOrigPtr ∨ outOrigPtr + (V_list.length - 1) ≤ a := by
      rcases hao with h_lt | h_ge
      · exact Or.inl h_lt
      · exact Or.inr (le_trans (Nat.add_le_add_left hVm1_le outOrigPtr) h_ge)
    have hab' : a < outBridgePtr ∨ outBridgePtr + 2 * ((V_list.length - 1) + inact.length) ≤ a := by
      rcases hab with h_lt | h_ge
      · exact Or.inl h_lt
      · exact Or.inr (le_trans (Nat.add_le_add_left hob_V_le outBridgePtr) h_ge)
    rw [hm12, hfr_s a ha_sim hao' hab' hah, hs11_lt_h3 a ha_h3, hpres a ha]
  have hs12_zero : ZeroFrom s12.mem (heap + lsstSpace Q_AN K_AN G.n G.m L_sim h) := by
    intro a ha
    have ha_sim : simHeap + simDecodeSpace Q_AN V_list.length m_aug L_sim h cost ≤ a := by
      have hsd := simDecodeSpace_mono (Q := Q_AN) (L_sim := L_sim) (h := h) hV_2m hm_aug_le hcost_bound
      exact le_trans (le_trans (Nat.add_le_add_left hsd _) hsimHeap_sp) ha
    rw [hm12]
    exact hz_sim a ha_sim
  have hs12_43 : s12.regs 43 = simHeap := by
    rw [hr12, Function.update_of_ne (by decide)]
    exact hs11_43
  have hs12_c1_lo : simHeap + 5 ≤ s12.mem (simHeap + 1) := by rw [hm12]; exact hsim_c1_lo
  have hs12_heap_le : heap ≤ s12.mem (simHeap + 1) := by linarith only [hheap_sim, hs12_c1_lo]
  have hs12_c1_le : s12.mem (simHeap + 1) ≤ heap + lsstSpace Q_AN K_AN G.n G.m L_sim h := by
    have hsd := simDecodeSpace_mono (Q := Q_AN) (L_sim := L_sim) (h := h) hV_2m hm_aug_le hcost_bound
    rw [hm12]
    exact le_trans hsim_c1_le (le_trans (Nat.add_le_add_left hsd _) hsimHeap_sp)
  have hs12_hz_c1 : ZeroFrom s12.mem (s12.mem (simHeap + 1)) := by rw [hm12]; exact hsim_hz_c1
  have hdec1_lt : ∀ e ∈ dec.1, e < G.m := decodeAN19Output_orig_lt G V_list B mult out
  have hdec12_le : dec.1.length + dec.2.length ≤ G.n - 1 :=
    decodeAN19Output_len_le G V_list B mult out hout_len hV_pos hVI_le
  have hs12_post : LSSTPost K_AN G v ℓ outOrigPtr outBridgePtr outHdrPtr heap mem_orig (.returned 0) s12.mem :=
    ⟨dec.1, dec.2, rfl, hm12.symm ▸ hhdr0_s, hm12.symm ▸ hhdr1_s, hdec1_len, hdec2_len,
      hdec1_lt, hdec12_le, hm12.symm ▸ hlo_s, hm12.symm ▸ hbr_s, hlsst, hs12_frame⟩
  refine htail s12 simHeap (s12.mem (simHeap + 1)) _ hs12_43 hs12_c1_lo rfl hs12_heap_le hs12_c1_le
    hs12_hz_c1 hs12_post hs12_zero ?_
  simp only [Expr.size, argsSize] at hk ⊢
  linarith only [hk]


end MinCostFlow.WideWord
