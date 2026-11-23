module

public import MinCostFlow.LowStretch.ProgPreG
public import MinCostFlow.LowStretch.ProgPreCLoop
public import MinCostFlow.LowStretch.ProgPreCMath
public import MinCostFlow.LowStretch.ProgLog

/-!
# The preprocessing, part 4: the record of the first cluster

`rP` computes the threshold `θ = thr S B n` of the first cluster from `S = max(μ, 4Bn)`, where `μ`
is the merge weight of the root and `B = PAR[2]`; the maximum is `μ + (4Bn - μ)`. Then it labels each vertex with the head of
its `θ`-node (`labP`), lists the `θ`-nodes (the node filter), writes the local index of each
node at its head (`locP`), and lists the pairs whose ends have different labels (the pair
filter). Last it writes `N`, `θ`, `log₂ θ`, the number of nodes and the number of pairs to the
five cells at `CTL` (`rP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM MinCostFlow.Cited

/-- `rP` with `args = [n, m, N]`. The called procedures sit at `bLog`, `bLab`, `bNod`, `bLoc` and
`bSa`. -/
def rP (bLog bLab bNod bLoc bSa : ℕ) : Stmt :=
  .seq (.assign 3 (.load (.bin .add (lin 8 9 13) (.reg 2))))
  (.seq (.assign 4 (.bin .mul (.bin .mul (.const 4) (.load (lin 4 3 0))) (.reg 0)))
  (.seq (.assign 5 (.bin .add (.reg 3) (.bin .sub (.reg 4) (.reg 3))))
  (.seq (.call 6 bLog [.bin .div (.reg 5) (.reg 4)])
  (.seq (.assign 7 (.bin .shiftLeft (.const 1) (.reg 6)))
  (.seq (.call 8 bLab [.reg 2, lin 15 11 30, lin 9 9 13, lin 9 9 7, .reg 7, lin 9 9 21])
  (.seq (.call 8 bNod [.reg 2, lin 15 11 28, lin 9 9 13, lin 9 9 7, .reg 7])
  (.seq (.call 9 bLoc [.reg 8, lin 15 11 32, lin 15 11 28, lin 9 9 21])
  (.seq (.call 9 bSa [.reg 1, lin 15 11 34, .const 2, lin 15 11 30])
  (.seq (.store (lin 10 11 28) (.reg 2))
  (.seq (.store (lin 11 11 28) (.reg 7))
  (.seq (.store (lin 12 11 28) (.reg 6))
  (.seq (.store (lin 13 11 28) (.reg 8))
  (.seq (.store (lin 14 11 28) (.reg 9))
  (.ret (.const 0)))))))))))))))

theorem rP_noRand (bLog bLab bNod bLoc bSa : ℕ) : (rP bLog bLab bNod bLoc bSa).NoRand := by
  simp [rP, lin, Stmt.NoRand]

/-- The number `S = max(μ, 4Bn)` of the threshold of the first cluster. -/
def rootS (T : KT) (G : WGraph) : ℕ := max (T.mw (T.N - 1)) (4 * pB G.n * G.n)

/-- The cost of `rP`. -/
def rCost (G : WGraph) (T : KT) : ℕ :=
  300 * (G.m + 2 * G.n + 1) + log2Cost (rootS T G / (4 * pB G.n * G.n))

/-- The contract of `rP` for the graph `G` and its merge tree `T`. -/
noncomputable def rC (w : ℕ) (G : WGraph) (T : KT) : Contract where
  pre args mem := args = [G.n, G.m, T.N] ∧ TreeIn w G T mem ∧
    (∀ k < T.N, mem (aHEAD G.n G.m + k) = T.hd (pgOf G) k) ∧ mem (aPAR G.n G.m + 2) = pB G.n ∧
    ZeroFrom mem (aCTL G.n G.m)
  post _ mem _ mem' :=
    mem' (aCTL G.n G.m) = T.N ∧ mem' (aCTL G.n G.m + 1) = rootθ T G ∧
    rootθ T G = 2 ^ mem' (aCTL G.n G.m + 2) ∧
    mem' (aCTL G.n G.m + 3) = (rootRec T G).nodes.length ∧
    mem' (aCTL G.n G.m + 4) = (rootRec T G).S.length ∧
    (∀ v < G.n, mem' (aLAB G.n G.m + v) = T.hd (pgOf G) (T.top (rootθ T G) v)) ∧
    (∀ k ∈ (rootRec T G).nodes, mem' (aLOC G.n G.m + T.hd (pgOf G) k) = (rootRec T G).nodes.idxOf k) ∧
    (∀ x < T.N, mem' (aLOC G.n G.m + x) < 2 ^ w) ∧
    ListAt mem' (aNODES G.n G.m) (rootRec T G).nodes ∧
    (∀ j < (rootRec T G).S.length, mem' (aSA G.n G.m + 2 * j) = ((rootRec T G).S.getD j (0, 0)).1 ∧
      mem' (aSA G.n G.m + 2 * j + 1) = ((rootRec T G).S.getD j (0, 0)).2) ∧
    ZeroFrom mem' (aH G.n G.m) ∧ ∀ a < aCTL G.n G.m, mem' a = mem a
  cost _ _ := rCost G T

/-- A cell of the memory, as a proposition that `omega` does not read. -/
def Cell (mem : ℕ → ℕ) (a v : ℕ) : Prop := mem a = v

set_option maxHeartbeats 2000000 in
theorem rP_spec {w : ℕ} {p : Program} {b bLog bLab bNod bLoc bSa : ℕ} {G : WGraph} {T : KT}
    (hp : p.HasAt b [rP bLog bLab bNod bLoc bSa]) (hLog : MeetsContract w p bLog (log2C w))
    (hLab : MeetsContract w p bLab (labC w T (pgOf G)))
    (hNod : MeetsContract w p bNod
      (filtC w (nodeE (.reg 15)) (.reg 15) 1 (nodesPre w) nodesC fun _ _ k => k))
    (hLoc : MeetsContract w p bLoc (locC w))
    (hSa : MeetsContract w p bSa (filtC w eDiff (.reg 15) 2 (saPre w) saC fun _ _ i => i)) :
    MeetsContract w p b (rC w G T) := by
  intro args mem pos ω _ hpre
  obtain ⟨rfl, hT, hHD, hB, hZ⟩ := hpre
  have hproc : p.procs[b]? = some (rP bLog bLab bNod bLoc bSa) := hp 0 (by simp)
  refine ⟨_, hproc, ?_⟩
  have hG := hT.input
  have hw := hG.add_lt
  have hn1 := hG.one_le
  have hN := hT.N_le
  have hok := hT.ok
  have hnN : G.n < T.N := hok.n_lt
  have hpar := hG.par_lt
  simp only [aH] at hw
  have hends := hG.ends
  have hpG : ∀ q < G.m, (pgOf G).pu q < G.n ∧ (pgOf G).pv q < G.n := fun q hq =>
    ⟨(hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).1,
      (hG.allowed.fit.ok q (by rw [pgOf_m]; exact hq)).2.1⟩
  have hμ : mem (8 + 9 * G.m + 13 * G.n + T.N) = T.mw (T.N - 1) := by
    have := (hT.par (T.N - 1) (by omega)).2; unfold aKMW at this
    rw [← this]; congr 1; omega
  have hμw : T.mw (T.N - 1) ≤ (pgOf G).maxω := KT.mw_le_maxω hok (by omega)
  have hB' : mem (4 + 3 * G.m + 0 * G.n) = pB G.n := by
    rw [← hB]; unfold aPAR; congr 1; omega
  have hBn : 4 * pB G.n * G.n ≤ 2 ^ 16 * (G.n + 4) ^ 4 := by
    have h3 := pB_le_poly G.n
    have h4 : G.n ≤ (G.n + 4) ^ 2 := (show G.n ≤ G.n + 4 by omega).trans (Nat.le_self_pow (by norm_num) _)
    calc 4 * pB G.n * G.n ≤ 4 * (64 * (G.n + 4) ^ 2) * (G.n + 4) ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 4 h3) h4
      _ = 256 * (G.n + 4) ^ 4 := by ring
      _ ≤ 2 ^ 16 * (G.n + 4) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
  have hB1 : 1 ≤ 4 * pB G.n * G.n := by
    have : 0 < pB G.n := by unfold pB pL; positivity
    have := Nat.mul_pos (Nat.mul_pos (by norm_num : 0 < 4) this) (by omega : 0 < G.n); omega
  have hPAR' : ∀ k < T.N, mem (9 + 9 * G.m + 7 * G.n + k) = T.par k := fun k hk => by
    have := (hT.par k hk).1; unfold aKPAR at this; exact this
  have hMW' : ∀ k < T.N, mem (9 + 9 * G.m + 13 * G.n + k) = T.mw k := fun k hk => by
    have := (hT.par k hk).2; unfold aKMW at this; exact this
  have hHD' : ∀ k < T.N, mem (9 + 9 * G.m + 21 * G.n + k) = T.hd (pgOf G) k := fun k hk => by
    have := hHD k hk; unfold aHEAD at this; exact this
  dsimp only [rP]
  have hBw : 4 * pB G.n * G.n < 2 ^ w := by omega
  clear hBn hpar
  generalize hBd : pB G.n = B at hBw hB1 hB' hB
  replace hμ : Cell mem (8 + 9 * G.m + 13 * G.n + T.N) (T.mw (T.N - 1)) := hμ
  replace hB' : Cell mem (4 + 3 * G.m + 0 * G.n) B := hB'
  clear hB
  refine runs_start_le ?_
  refine runs_seq_assign_le (v := T.mw (T.N - 1)) ?_ ?_
  · refine Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_const ?_)
      (Expr.eval_mul (Expr.eval_const ?_) (Expr.eval_reg_of_eq rfl) ?_) ?_)
      (Expr.eval_mul (Expr.eval_const ?_) (Expr.eval_reg_of_eq rfl) ?_) ?_) (Expr.eval_reg_of_eq rfl) ?_) hμ
    all_goals (try simp only [startState, List.getD_cons_zero, List.getD_cons_succ])
    all_goals omega
  have c4 : 4 < 2 ^ w := by omega
  have cB : 4 * B < 2 ^ w := by
    have : 4 * B ≤ 4 * B * G.n := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have cP : 4 + 3 * G.m + 0 * G.n + 3 + 0 < 2 ^ w := by omega
  have eP := lin_eval (w := w) (c := 4) (u := 3) (v := 0)
    (st := { (startState [G.n, G.m, T.N] mem pos) with
      regs := Function.update (startState [G.n, G.m, T.N] mem pos).regs 3 (T.mw (T.N - 1)) })
    (n := G.n) (m := G.m) rfl rfl cP
  refine runs_seq_assign_le (v := 4 * B * G.n) (Expr.eval_mul (Expr.eval_mul (Expr.eval_const c4)
    (Expr.eval_load_of_eq eP hB') cB) (Expr.eval_reg_of_eq rfl) hBw) ?_
  unfold lin
  -- the threshold
  have hS : T.mw (T.N - 1) + (4 * B * G.n - T.mw (T.N - 1)) = rootS T G := by
    unfold rootS; rw [hBd]; omega
  have hSw : rootS T G < 2 ^ w := by unfold rootS; rw [hBd]; omega
  have hS1 : 1 ≤ rootS T G / (4 * B * G.n) :=
    (Nat.one_le_div_iff (by omega)).mpr (by unfold rootS; rw [hBd]; omega)
  have hSle : rootS T G / (4 * B * G.n) ≤ rootS T G := Nat.div_le_self _ _
  have hw2 := hG.two_le_w
  wram_step
  wram_step
  · exact ⟨_, rfl, hS1, by omega, hw2⟩
  intro lθ mem1 pos1 h1
  obtain ⟨rfl, rfl⟩ := h1
  have hθ : rootθ T G = 2 ^ Nat.log 2 (rootS T G / (4 * B * G.n)) := by
    unfold rootθ thr rootS; rw [hBd]
  have hθw : 2 ^ Nat.log 2 (rootS T G / (4 * B * G.n)) < 2 ^ w :=
    lt_of_le_of_lt ((Nat.pow_log_le_self 2 (by omega)).trans hSle) hSw
  have hsh : 1 <<< Nat.log 2 (rootS T G / (4 * B * G.n)) = rootθ T G := by
    rw [Nat.one_shiftLeft, hθ]
  wram_step
  wram_step
  · refine ⟨T.N, _, _, _, _, _, rfl, hok, rfl, one_le_rootθ, fun k hk => ⟨?_, ?_, ?_⟩, by omega,
      by omega, by omega, by omega⟩
    · exact hMW' k hk
    · exact hPAR' k hk
    · exact hHD' k hk
  intro v2 mem2 pos2 h2
  obtain ⟨h2a, h2b⟩ := h2 _ _ _ _ _ _ rfl
  have hin2 : ∀ a < 15 + 11 * G.m + 30 * G.n, mem2 a = mem1 a := fun a ha => h2b a (Or.inl ha)
  have hlab : ∀ v < G.n, mem2 (15 + 11 * G.m + 30 * G.n + v) = T.hd (pgOf G) (T.top (rootθ T G) v) :=
    h2a
  have hC : ∀ k < T.N, nodesC [T.N, 15 + 11 * G.m + 28 * G.n, 9 + 9 * G.m + 13 * G.n,
      9 + 9 * G.m + 7 * G.n, rootθ T G] mem2 k ≠ 0 ↔ T.IsNode (rootθ T G) k := by
    intro k hk
    have hpk : T.par k < T.N := by
      by_cases h : k + 1 < T.N
      · exact (hok.par_lt k h).2
      · have : k = T.N - 1 := by omega
        rw [this, hok.root]; omega
    unfold nodesC KT.IsNode
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    have e1 : mem2 (9 + 9 * G.m + 13 * G.n + k) = T.mw k := by rw [hin2 _ (by omega), hMW' k hk]
    have e2 : mem2 (9 + 9 * G.m + 7 * G.n + k) = T.par k := by rw [hin2 _ (by omega), hPAR' k hk]
    have e3 : mem2 (9 + 9 * G.m + 13 * G.n + T.par k) = T.mw (T.par k) := by
      rw [hin2 _ (by omega), hMW' _ hpk]
    rw [e2, e3, e1]
    split_ifs with h
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]; exact ⟨hk, h⟩
    · simp only [ne_eq, not_true_eq_false, false_iff]; exact fun h' => h h'.2
  have hkept := kept_nodes hC
  have hsN := kept_length_le (nodesC [T.N, 15 + 11 * G.m + 28 * G.n, 9 + 9 * G.m + 13 * G.n,
      9 + 9 * G.m + 7 * G.n, rootθ T G] mem2) T.N
  rw [hkept] at hsN
  -- the nodes
  wram_step
  · refine ⟨⟨_, _, _, _, _, rfl, by omega, by omega, by omega, fun k hk => ?_⟩, by simp, le_rfl,
      by simp; omega⟩
    show mem2 _ < _
    rw [hin2 _ (by omega), hPAR' k hk]
    by_cases h : k + 1 < T.N
    · exact (hok.par_lt k h).2
    · have : k = T.N - 1 := by omega
      rw [this, hok.root]; omega
  intro s mem3 pos3 h3
  obtain ⟨hs, h3a, h3b⟩ := h3
  simp only [List.getD_cons_zero, List.getD_cons_succ, hkept, Nat.one_mul] at hs h3a h3b
  set L := (rootRec T G).nodes with hL
  have hin3 : ∀ a, (a < 15 + 11 * G.m + 28 * G.n ∨ 15 + 11 * G.m + 28 * G.n + T.N ≤ a) →
      mem3 a = mem2 a := fun a ha => h3b a (fun j hj => by omega)
  have hLnode : ∀ i < L.length, T.IsNode (rootθ T G) (L.getD i 0) := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact mem_rootRec_nodes.mp (List.getElem_mem hi)
  have hLnd : L.Nodup := by rw [hL]; unfold rootRec; exact (List.nodup_range).filter _
  have hhd : ∀ i < L.length, hdAt mem3 (15 + 11 * G.m + 28 * G.n) (9 + 9 * G.m + 21 * G.n) i =
      T.hd (pgOf G) (L.getD i 0) := fun i hi => by
    have hk := (hLnode i hi).1
    unfold hdAt
    rw [h3a i hi, hin3 _ (Or.inl (by omega)), hin2 _ (by omega), hHD' _ hk]
  have hhdN : ∀ i < L.length, T.hd (pgOf G) (L.getD i 0) < T.N := fun i hi =>
    KT.hd_lt hok (hLnode i hi).1
  -- the local indices
  wram_step
  · dsimp only
    refine ⟨_, _, _, _, rfl, by omega, fun i hi => ?_, fun i hi => ?_, fun i hi j hj hij => ?_,
      by omega⟩
    · rw [h3a i (by omega)]; have := (hLnode i (by omega)).1; omega
    · rw [hhd i (by omega)]; have := hhdN i (by omega); omega
    · rw [hhd i (by omega), hhd j (by omega)]
      refine (hLnode i (by omega)).hd_ne hok (hLnode j (by omega)) fun he => hij ?_
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
      exact (hLnd.getElem_inj_iff).mp he
  intro v4 mem4 pos4 h4
  obtain ⟨h4a, h4b⟩ := h4 _ _ _ _ rfl
  dsimp only at h4a h4b
  have hin4 : ∀ a, (a < 15 + 11 * G.m + 32 * G.n ∨ 15 + 11 * G.m + 32 * G.n + T.N ≤ a) →
      mem4 a = mem3 a := fun a ha => h4b a (fun i hi => by
        rw [hhd i (by omega)]; have := hhdN i (by omega); omega)
  have hin41 : ∀ a < 15 + 11 * G.m + 28 * G.n, mem4 a = mem1 a := fun a ha => by
    rw [hin4 a (Or.inl (by omega)), hin3 a (Or.inl ha), hin2 a (by omega)]
  have hlab4 : ∀ v < G.n, mem4 (15 + 11 * G.m + 30 * G.n + v) =
      T.hd (pgOf G) (T.top (rootθ T G) v) := fun v hv => by
    rw [hin4 _ (Or.inl (by omega)), hin3 _ (Or.inr (by omega)), hlab v hv]
  have hend4 : ∀ q < G.m, mem4 (2 + 3 * q) = (pgOf G).pu q ∧ mem4 (2 + 3 * q + 1) = (pgOf G).pv q :=
    fun q hq => by rw [hin41 _ (by omega), hin41 _ (by omega)]; exact hends q hq
  have hCS : ∀ q < G.m, saC [G.m, 15 + 11 * G.m + 34 * G.n, 2, 15 + 11 * G.m + 30 * G.n] mem4 q ≠ 0 ↔
      T.top (rootθ T G) ((pgOf G).pu q) ≠ T.top (rootθ T G) ((pgOf G).pv q) := by
    intro q hq
    unfold saC
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [(hend4 q hq).1, (hend4 q hq).2, hlab4 _ (hpG q hq).1, hlab4 _ (hpG q hq).2]
    split_ifs with h
    · simp only [ne_eq, not_true_eq_false, false_iff, Decidable.not_not]
      by_contra hne
      exact (KT.isNode_top hok (hpG q hq).1 one_le_rootθ).hd_ne hok
        (KT.isNode_top hok (hpG q hq).2 one_le_rootθ) hne h
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
      exact fun he => h (by rw [he])
  have hkS := kept_pairs hCS
  -- the pairs
  wram_step
  · refine ⟨⟨_, _, _, _, G.n, rfl, by omega, by omega, by omega, fun i hi => ?_⟩, by simp, by omega,
      by simp; omega⟩
    dsimp only
    rw [(hend4 i hi).1, (hend4 i hi).2]; exact hpG i hi
  intro nS mem5 pos5 h5
  obtain ⟨hnS, h5a, h5b⟩ := h5
  simp only [List.getD_cons_zero, List.getD_cons_succ, hkS, List.length_map] at hnS h5a h5b
  set S := (rootRec T G).S with hSdef
  have hSm : S.length ≤ G.m := by
    have := kept_length_le (saC [G.m, 15 + 11 * G.m + 34 * G.n, 2, 15 + 11 * G.m + 30 * G.n] mem4) G.m
    rw [hkS, List.length_map] at this; exact this
  have hlo5 : ∀ a < 15 + 11 * G.m + 34 * G.n, mem5 a = mem4 a := fun a ha => h5b a (fun j hj => by omega)
  have hhi5 : ∀ a, 15 + 11 * G.m + 32 * G.n + T.N ≤ a → (∀ j < S.length, a ≠ 15 + 11 * G.m + 34 * G.n + 2 * j) →
      mem5 a = mem1 a := fun a ha hne => by
    rw [h5b a hne, hin4 a (Or.inr ha), hin3 a (Or.inr (by omega)), h2b a (Or.inr (by omega))]
  have hlow : ∀ a < 15 + 11 * G.m + 28 * G.n, mem5 a = mem1 a := fun a ha => by
    rw [hlo5 a (by omega), hin41 a ha]
  -- the five cells
  wram_run
  · dsimp only
    have hsh' : 1 <<< Nat.log 2 (rootS T G / (4 * B * G.n)) = rootθ T G := hsh
    rw [hsh']
    refine ⟨?_, ?_, ?_, ?_, ?_, fun v hv => ?_, fun k hk => ?_, fun x hx => ?_, fun i hi => ?_, fun j hj => ⟨?_, ?_⟩,
      fun a ha => ?_, fun a ha => ?_⟩
    all_goals simp only [Function.update_apply, aCTL, aLAB, aLOC, aNODES, aSA, aH]
    all_goals (try simp only [aH, aCTL] at ha)
    all_goals (split_ifs <;> first | rfl | omega | exact hθ | exact hs | exact hnS | skip)
    · rw [hlo5 _ (by omega), hlab4 v hv]
    · have hi : L.idxOf k < L.length := List.idxOf_lt_length_of_mem hk
      have hg : L.getD (L.idxOf k) 0 = k := by
        rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf]
      have hkN : T.hd (pgOf G) k < T.N := by rw [← hg]; exact hhdN _ hi
      have := h4a _ hi
      rw [hhd _ hi, hg] at this
      rw [hlo5 _ (by omega), this]
    · rw [hlo5 _ (by omega)]
      by_cases hx' : ∃ i < L.length, x = T.hd (pgOf G) (L.getD i 0)
      · obtain ⟨i, hi, rfl⟩ := hx'
        have := h4a i hi
        rw [hhd i hi] at this
        rw [this]; omega
      · have hz := hZ (15 + 11 * G.m + 32 * G.n + x) (by unfold aCTL; omega)
        rw [h4b _ (fun i hi he => hx' ⟨i, hi, by rw [hhd i hi] at he; omega⟩),
          hin3 _ (Or.inr (by omega)), h2b _ (Or.inr (by omega))]
        simp only [startState] at hz ⊢
        omega
    · have h1 : i < T.N := lt_of_lt_of_le hi hsN
      rw [hlo5 _ (by omega), hin4 _ (Or.inl (by omega)), h3a i hi, List.getD_eq_getElem _ _ hi]
    · rw [h5a j (by omega), rootRec_S_fst_getD]
    · rw [rootRec_S_snd, hhi5 _ (by omega) (fun j' hj' => by omega)]
      exact hZ _ (by unfold aCTL; omega)
    · rw [hhi5 _ (by omega) (fun j' hj' => by omega)]
      exact hZ _ (by unfold aCTL; omega)
    · exact hlow a (by omega)
  · simp only [rC, rCost, log2C, labC, filtC, locC, List.getD_cons_zero, List.getD_cons_succ,
      Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons, argsSize_nil,
      nodeE, eDiff, eEnd0, eEnd1, hBd]
    omega

end MinCostFlow.LowStretch
