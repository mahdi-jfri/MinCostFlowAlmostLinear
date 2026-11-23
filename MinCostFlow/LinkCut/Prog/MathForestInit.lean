module

public import MinCostFlow.LinkCut.Prog.MathForestProcs

/-!
# Basic LCT procedures, deterministic `init`, and Word-RAM operation entry/exit framing

Defines:
- `LctProcs`, `LctProcs.atBase`, `LctProcs.op`, and `LctBaseOk`: procedure table layout
  for `MathForest` Link-Cut trees;
- `lctInitBody`: deterministic `O(n)` initialization independent of `L` (`lctInit_runs`,
  `lctInitBody_noRand`);
- `enterOp_ready` and `exitOp_rep`: entry/exit memory and `LctMemRep` / `DSRep.Respects`
  framing across caller answer buffers `[hp_caller, hp_eff)` and bump allocations;
- `splayForest_lct_runs`: splay execution combining `splayForest_runs` and `splay_safeExec`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section InitProcedure

private theorem freeSlotChain_init {mem : ℕ → ℕ} {nb n : ℕ}
    (hnext : ∀ i < n, nodeField mem nb (n + 1 + i) OFF_EU =
      if i + 1 = n then 0 else n + 1 + (i + 1)) :
    ∀ m a, m + a = n →
      FreeSlotChain mem nb (if m = 0 then 0 else n + 1 + a) ((List.range m).map (n + 1 + a + ·)) := by
  intro m
  induction m with
  | zero =>
      intro a _
      simp [FreeSlotChain]
  | succ m ih =>
      intro a hma
      have ha_lt : a < n := by omega
      rw [List.range_succ_eq_map, List.map_cons]
      simp only [Nat.add_zero, List.map_map, FreeSlotChain, Nat.succ_ne_zero, ↓reduceIte, true_and]
      rw [hnext a ha_lt]
      have hiff : a + 1 = n ↔ m = 0 := by omega
      have hlist : (List.range m).map ((fun x => n + 1 + a + x) ∘ Nat.succ) =
          (List.range m).map (n + 1 + (a + 1) + ·) := by
        refine List.map_congr_left fun k _ => ?_
        dsimp only [Function.comp_apply]; omega
      rw [hlist]
      by_cases hm0 : m = 0
      · have han : a + 1 = n := hiff.mpr hm0
        simp only [han, ↓reduceIte, hm0]
        simpa [hm0] using ih (a + 1) (by omega)
      · have han : a + 1 ≠ n := mt hiff.mp hm0
        simp only [han, ↓reduceIte]
        simpa [hm0] using ih (a + 1) (by omega)

private theorem initTrees_perm_nodes (cap : ℕ) :
    (((List.range cap).map fun i => AuxTree.node (i + 1) .leaf .leaf).flatMap AuxTree.toList).Perm
      ((List.range cap).map (· + 1)) := by
  have hfl : (((List.range cap).map fun i => AuxTree.node (i + 1) .leaf .leaf).flatMap
      AuxTree.toList) = (List.range cap).map (· + 1) := by
    induction cap with
    | zero => simp
    | succ k ih =>
        simp only [List.range_succ, List.map_append, List.map_singleton, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, ih, AuxTree.toList]
        simp
  rw [hfl]

private theorem init_readAuxTree_eq {mem : ℕ → ℕ} {nb cap : ℕ}
    (hzch : ∀ u, 1 ≤ u → u ≤ cap → nodeField mem nb u OFF_LEFT = 0 ∧ nodeField mem nb u OFF_RIGHT = 0)
    {fuel u : ℕ} (hf1 : 1 ≤ fuel) (hu1 : 1 ≤ u) (hu2 : u ≤ cap) :
    readAuxTree mem nb cap fuel u = AuxTree.node u .leaf .leaf := by
  obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
  obtain ⟨u', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  have hlr := hzch (u' + 1) hu1 hu2
  simp [readAuxTree, hu2, hlr.1, hlr.2]

private theorem init_phi_zero {mem : ℕ → ℕ} {b n L : ℕ}
    (hzch : ∀ u, 1 ≤ u → u ≤ lctCap n →
      nodeField mem (lctNodesBase b) u OFF_LEFT = 0 ∧
      nodeField mem (lctNodesBase b) u OFF_RIGHT = 0 ∧
      nodeField mem (lctNodesBase b) u OFF_PPAR = 0) :
    lctPhi L mem b n = 0 := by
  unfold lctPhi splayMemPhi lctHeavyCount
  have hv0 : ∀ y, 1 ≤ y → y ≤ lctCap n → lctVSize mem (lctNodesBase b) (lctCap n) y = 0 := by
    intro y hy1 hy2
    unfold lctVSize
    apply List.sum_eq_zero
    intro s hs
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hs
    rcases hs with ⟨r, ⟨hr_mem, hpp⟩, rfl⟩
    simp only [auxRootIds, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq] at hr_mem
    rcases hr_mem with ⟨⟨i, hi, rfl⟩, _⟩
    have := (hzch (i + 1) (by omega) (by omega)).2.2
    omega
  have hsplay : ((auxRootIds mem (lctNodesBase b) (lctCap n)).map fun r =>
      (readAuxTree mem (lctNodesBase b) (lctCap n) (lctCap n) r).treePhi
        (lctVSize mem (lctNodesBase b) (lctCap n))).sum = 0 := by
    apply List.sum_eq_zero
    intro s hs
    simp only [List.mem_map] at hs
    rcases hs with ⟨r, hr_mem, rfl⟩
    simp only [auxRootIds, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq] at hr_mem
    rcases hr_mem with ⟨⟨i, hi, rfl⟩, _⟩
    have hcap1 : 1 ≤ lctCap n := by omega
    rw [init_readAuxTree_eq (fun u h1 h2 => ⟨(hzch u h1 h2).1, (hzch u h1 h2).2.1⟩)
      hcap1 (by omega) (by omega)]
    simp [AuxTree.treePhi, AuxTree.rank, AuxTree.treeSize, hv0 (i + 1) (by omega) (by omega)]
  have hheavy : ((auxRootIds mem (lctNodesBase b) (lctCap n)).filter fun r =>
      isHeavyRoot mem (lctNodesBase b) (lctCap n) r) = [] := by
    rw [List.filter_eq_nil_iff]
    intro r hr
    simp only [auxRootIds, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq] at hr
    rcases hr with ⟨⟨i, hi, rfl⟩, _⟩
    have hpp0 := (hzch (i + 1) (by omega) (by omega)).2.2
    simp [isHeavyRoot, hpp0]
  rw [hsplay, hheavy]
  simp

private def lctInitConc (b n : ℕ) : LctConc where
  n := n
  trees := (List.range (lctCap n)).map fun i => AuxTree.node (i + 1) .leaf .leaf
  freeEdges := (List.range n).map (n + 1 + ·)
  edgeMap := []
  regions := []
  hpHi := lctArenaHi b (lctCap n)

private theorem addr_inj_stride {nb u v off1 off2 : ℕ}
    (h1 : off1 < NODE_STRIDE) (h2 : off2 < NODE_STRIDE)
    (heq : nb + NODE_STRIDE * u + off1 = nb + NODE_STRIDE * v + off2) :
    u = v ∧ off1 = off2 := by
  unfold NODE_STRIDE at h1 h2 heq
  exact ⟨by omega, by omega⟩

private theorem lctInit_loop1_triple {w L P b n : ℕ} (p : Program)
    (mem₀ : ℕ → ℕ) (hw : 1 < 2 ^ w)
    (hb_w : b + lctArenaWords n < 2 ^ w)
    (hz₀ : ∀ a, b ≤ a → mem₀ a = 0) :
    let nb := lctNodesBase b
    let cap := lctCap n
    let arenaHi := lctArenaHi b cap
    let memH := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update mem₀ (b + LCT_HDR_N) n)
        (b + LCT_HDR_CAP) cap)
        (b + LCT_HDR_FREE) (if n = 0 then 0 else n + 1))
        (b + LCT_HDR_L) L)
        (b + LCT_HDR_P) P)
        (b + LCT_HDR_HP) arenaHi
    Triple w p
      (fun st => st.mem = memH ∧ st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧
        st.regs 3 = cap ∧ st.regs 4 = arenaHi)
      (forRange 5 (.const 0) (.reg 0)
        (Stmt.assign 6 (.bin .add (.reg 5) (.const 1)) ;;
         Stmt.assign 7 (nodePtrExpr 2 6) ;;
         Stmt.store (fieldAddrExpr 7 OFF_ISV) (.const 1) ;;
         Stmt.store (fieldAddrExpr 7 OFF_VCNT) (.const 1)))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧ st.regs 4 = arenaHi ∧
        (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
        (∀ u ≤ cap, ∀ off < NODE_STRIDE,
          nodeField st.mem nb u off =
            if (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1 else 0))
      (fun _ => n * (40 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
  intro nb cap arenaHi memH
  have harena_w : arenaHi < 2 ^ w := by
    simpa [arenaHi, cap, lctArenaWords_eq] using hb_w
  have hn_w : n < 2 ^ w := by
    dsimp only [arenaHi, nb, cap] at harena_w
    unfold lctArenaHi lctNodesBase LCT_HDR_SIZE lctCap NODE_STRIDE at harena_w
    omega
  have hnb_w : nb < 2 ^ w := by
    dsimp only [arenaHi, nb] at harena_w
    unfold lctArenaHi at harena_w; omega
  have hmH_lt : ∀ a, a < b ∨ arenaHi ≤ a → memH a = mem₀ a := by
    intro a ha
    have hlt_ar : b + LCT_HDR_HP < arenaHi := by
      dsimp only [arenaHi, cap]
      unfold lctArenaHi lctNodesBase LCT_HDR_SIZE LCT_HDR_HP NODE_STRIDE; omega
    have hne : ∀ k ≤ 5, a ≠ b + k := by
      intro k hk
      dsimp only [arenaHi, cap] at ha
      rcases ha with ha | ha
      · omega
      · unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at ha; omega
    dsimp only [memH]
    unfold LCT_HDR_N LCT_HDR_CAP LCT_HDR_FREE LCT_HDR_L LCT_HDR_P LCT_HDR_HP
    rw [Function.update_of_ne (hne 5 (by decide)), Function.update_of_ne (hne 4 (by decide)),
      Function.update_of_ne (hne 3 (by decide)), Function.update_of_ne (hne 2 (by decide)),
      Function.update_of_ne (hne 1 (by decide)), Function.update_of_ne (hne 0 (by decide))]
  have hmH_zero_nodes : ∀ u ≤ cap, ∀ off < NODE_STRIDE, memH (nb + NODE_STRIDE * u + off) = 0 := by
    intro u hu off hoff
    have hge : b + 5 < nb + NODE_STRIDE * u + off := by
      unfold nb lctNodesBase LCT_HDR_SIZE; omega
    have hge_b : b ≤ nb + NODE_STRIDE * u + off := by omega
    have hne : ∀ k ≤ 5, nb + NODE_STRIDE * u + off ≠ b + k := fun k hk => by omega
    dsimp only [memH]
    unfold LCT_HDR_N LCT_HDR_CAP LCT_HDR_FREE LCT_HDR_L LCT_HDR_P LCT_HDR_HP
    rw [Function.update_of_ne (hne 5 (by decide)), Function.update_of_ne (hne 4 (by decide)),
      Function.update_of_ne (hne 3 (by decide)), Function.update_of_ne (hne 2 (by decide)),
      Function.update_of_ne (hne 1 (by decide)), Function.update_of_ne (hne 0 (by decide))]
    exact hz₀ _ hge_b
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧ st.regs 4 = arenaHi ∧
    st.regs 5 = i ∧ i ≤ n ∧
    (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
    (∀ u ≤ cap, ∀ off < NODE_STRIDE,
      nodeField st.mem nb u off =
        if (1 ≤ u ∧ u ≤ i) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1 else 0)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 5) (lo := .const 0) (hi := .reg 0)
    (P := fun st => st.mem = memH ∧ st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧
      st.regs 3 = cap ∧ st.regs 4 = arenaHi)
    (Inv := Inv) 40 0 n (Nat.zero_le n) hw (fun _ => hn_w)
    (fun st ⟨hm, hr0, hr1, hr2, hr3, hr4⟩ => by
      refine ⟨by simp [Expr.eval], ?_⟩
      refine ⟨by simpa using hr0, by simpa using hr1, by simpa using hr2, by simpa using hr3,
        by simpa using hr4, by simp, Nat.zero_le n, fun a _ => by simp [hm], fun a ha => ?_,
        fun u hu off hoff => ?_⟩
      · simp only [hm]
        rw [hmH_lt a (Or.inr ha)]
        dsimp only [arenaHi, cap] at ha
        exact hz₀ a (by unfold lctArenaHi lctNodesBase LCT_HDR_SIZE NODE_STRIDE at ha; omega)
      · have hfalse : ¬ ((1 ≤ u ∧ u ≤ 0) ∧ (off = OFF_ISV ∨ off = OFF_VCNT)) := by omega
        simp only [hfalse, ↓reduceIte]
        rw [nodeField, hm]
        exact hmH_zero_nodes u hu off hoff)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h0 : st.regs 0 = n := hi.1
      simp [Expr.eval, h0])
    (fun i hi0 hin => by
      intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, _, hlt_nb, hge_ar, hfld⟩
      have hi1_w : i + 1 < 2 ^ w := lt_of_le_of_lt hin hn_w
      have hptr_lt : nb + NODE_STRIDE * (i + 1) + OFF_VCNT < arenaHi := by
        dsimp only [arenaHi, cap]
        unfold lctArenaHi lctCap NODE_STRIDE OFF_VCNT
        nlinarith
      have hptr_w : nb + NODE_STRIDE * (i + 1) < 2 ^ w := by omega
      have hst_w : NODE_STRIDE * (i + 1) < 2 ^ w := by omega
      have hns_w : NODE_STRIDE < 2 ^ w := by
        have : 1 ≤ i + 1 := by omega
        have : NODE_STRIDE ≤ NODE_STRIDE * (i + 1) := Nat.le_mul_of_pos_right _ this
        omega
      have h1_w : 1 < 2 ^ w := hw
      let st1 := { st with regs := Function.update st.regs 6 (i + 1) }
      let st2 := { st1 with regs := Function.update st1.regs 7 (nb + NODE_STRIDE * (i + 1)) }
      let st3 := { st2 with mem := Function.update st2.mem (nb + NODE_STRIDE * (i + 1) + OFF_ISV) 1 }
      let st4 := { st3 with mem := Function.update st3.mem (nb + NODE_STRIDE * (i + 1) + OFF_VCNT) 1 }
      have hrun1 : Runs w p ω (Stmt.assign 6 (.bin .add (.reg 5) (.const 1))) st .normal st1 4 := by
        refine runs_assign_iff.mpr ⟨i + 1, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, hr5, h1_w, hi1_w]
      have hrun2 : Runs w p ω (Stmt.assign 7 (nodePtrExpr 2 6)) st1 .normal st2 6 := by
        refine runs_assign_iff.mpr ⟨nb + NODE_STRIDE * (i + 1), ?_, rfl, rfl, rfl⟩
        simp [nodePtrExpr, Expr.eval, st1, Function.update_of_ne, Function.update_self,
          hr2, hns_w, hst_w, hptr_w]
      have hrun3 : Runs w p ω (Stmt.store (fieldAddrExpr 7 OFF_ISV) (.const 1)) st2 .normal st3 5 := by
        refine runs_store_iff.mpr ⟨nb + NODE_STRIDE * (i + 1) + OFF_ISV, 1, ?_, ?_, rfl, rfl, rfl⟩
        · have h1v : nb + NODE_STRIDE * (i + 1) + OFF_ISV < 2 ^ w := by
            have hlt1 : nb + NODE_STRIDE * (i + 1) + OFF_ISV < arenaHi := by
              have : OFF_ISV < OFF_VCNT := by decide
              omega
            exact lt_trans hlt1 harena_w
          have hoff_w : OFF_ISV < 2 ^ w := by
            unfold OFF_ISV; exact lt_of_le_of_lt (by decide : 5 ≤ 30) (by simpa [NODE_STRIDE] using hns_w)
          simp [fieldAddrExpr, Expr.eval, st2, Function.update_self, hoff_w, h1v]
        · simp [Expr.eval, h1_w]
      have hrun4 : Runs w p ω (Stmt.store (fieldAddrExpr 7 OFF_VCNT) (.const 1)) st3 .normal st4 5 := by
        refine runs_store_iff.mpr ⟨nb + NODE_STRIDE * (i + 1) + OFF_VCNT, 1, ?_, ?_, rfl, rfl, rfl⟩
        · have h2v : nb + NODE_STRIDE * (i + 1) + OFF_VCNT < 2 ^ w := lt_trans hptr_lt harena_w
          have hoff_w : OFF_VCNT < 2 ^ w := by
            unfold OFF_VCNT; exact lt_of_le_of_lt (by decide : 6 ≤ 30) (by simpa [NODE_STRIDE] using hns_w)
          simp [fieldAddrExpr, Expr.eval, st3, st2, Function.update_self, hoff_w, h2v]
        · simp [Expr.eval, h1_w]
      have hseq := runs_seq_normal hrun1 (runs_seq_normal hrun2 (runs_seq_normal hrun3 hrun4))
      refine ⟨.normal, st4, _, hseq, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by dsimp only; omega⟩
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr0
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr1
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr2
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr3
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr4
      · simp [st4, st3, st2, st1]
      · omega
      · intro a ha
        have ha1 : a ≠ nb + NODE_STRIDE * (i + 1) + OFF_ISV := by omega
        have ha2 : a ≠ nb + NODE_STRIDE * (i + 1) + OFF_VCNT := by omega
        simpa [st4, st3, st2, st1, Function.update_of_ne ha1, Function.update_of_ne ha2] using hlt_nb a ha
      · intro a ha
        have ha1 : a ≠ nb + NODE_STRIDE * (i + 1) + OFF_ISV := by
          have : OFF_ISV < OFF_VCNT := by decide
          omega
        have ha2 : a ≠ nb + NODE_STRIDE * (i + 1) + OFF_VCNT := by omega
        simpa [st4, st3, st2, st1, Function.update_of_ne ha1, Function.update_of_ne ha2] using hge_ar a ha
      · intro u hu off hoff
        have haddr : nb + NODE_STRIDE * u + off = nb + NODE_STRIDE * (i + 1) + OFF_VCNT ↔
            u = i + 1 ∧ off = OFF_VCNT :=
          ⟨addr_inj_stride hoff (by decide), by rintro ⟨rfl, rfl⟩; rfl⟩
        have haddr2 : nb + NODE_STRIDE * u + off = nb + NODE_STRIDE * (i + 1) + OFF_ISV ↔
            u = i + 1 ∧ off = OFF_ISV :=
          ⟨addr_inj_stride hoff (by decide), by rintro ⟨rfl, rfl⟩; rfl⟩
        dsimp only [nodeField, st4, st3, st2, st1]
        by_cases huc : u = i + 1 ∧ off = OFF_VCNT
        · rcases huc with ⟨rfl, rfl⟩
          simp [Function.update_self]
        · rw [Function.update_of_ne (mt haddr.mp huc)]
          by_cases hui : u = i + 1 ∧ off = OFF_ISV
          · rcases hui with ⟨rfl, rfl⟩
            simp [Function.update_self]
          · rw [Function.update_of_ne (mt haddr2.mp hui)]
            have hprev := hfld u hu off hoff
            dsimp only [nodeField] at hprev
            rw [hprev]
            by_cases h1 : (1 ≤ u ∧ u ≤ i) ∧ (off = OFF_ISV ∨ off = OFF_VCNT)
            · have h2 : (1 ≤ u ∧ u ≤ i + 1) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) :=
                ⟨⟨h1.1.1, by omega⟩, h1.2⟩
              simp [h1, h2]
            · by_cases h2 : (1 ≤ u ∧ u ≤ i + 1) ∧ (off = OFF_ISV ∨ off = OFF_VCNT)
              · exfalso
                rcases (by omega : u ≤ i ∨ u = i + 1) with hle' | rfl
                · exact h1 ⟨⟨h2.1.1, hle'⟩, h2.2⟩
                · rcases h2.2 with rfl | rfl
                  · exact hui ⟨rfl, rfl⟩
                  · exact huc ⟨rfl, rfl⟩
              · simp [h1, h2]
      · simpa [st4, st3, st2, st1, Function.update_of_ne] using hr5)
  exact hloop.conseq (fun _ h => h)
    (fun o st => match o with
      | .normal => fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
          h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩
      | .returned _ => False.elim)
    (fun _ _ => le_rfl)

private theorem lctInit_loop2_triple {w b n : ℕ} (p : Program)
    (hw : 1 < 2 ^ w) (hb_w : b + lctArenaWords n < 2 ^ w)
    (memH : ℕ → ℕ) :
    let nb := lctNodesBase b
    let cap := lctCap n
    let arenaHi := lctArenaHi b cap
    Triple w p
      (fun st => st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧
        st.regs 4 = arenaHi ∧ (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
        (∀ u ≤ cap, ∀ off < NODE_STRIDE,
          nodeField st.mem nb u off =
            if (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1 else 0))
      (forRange 5 (.const 0) (.reg 0)
        (Stmt.assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 5)) ;;
         Stmt.assign 7 (nodePtrExpr 2 6) ;;
         Stmt.store (fieldAddrExpr 7 OFF_EU)
           (.bin .mul (.bin .sub (.const 1) (.bin .eq (.bin .add (.reg 5) (.const 1)) (.reg 0)))
             (.bin .add (.reg 6) (.const 1)))))
      (normalPost fun st =>
        st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧ st.regs 4 = arenaHi ∧
        (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
        (∀ u ≤ cap, ∀ off < NODE_STRIDE,
          nodeField st.mem nb u off =
            if (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1
            else if (n + 1 ≤ u ∧ u ≤ cap) ∧ off = OFF_EU then
              if u = cap then 0 else u + 1
            else 0))
      (fun _ => n * (45 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
  intro nb cap arenaHi
  have harena_w : arenaHi < 2 ^ w := by simpa [arenaHi, cap, lctArenaWords_eq] using hb_w
  have hn_w : n < 2 ^ w := by
    dsimp only [arenaHi, nb, cap] at harena_w
    unfold lctArenaHi lctNodesBase LCT_HDR_SIZE lctCap NODE_STRIDE at harena_w; omega
  have hnb_w : nb < 2 ^ w := by
    dsimp only [arenaHi, nb] at harena_w
    unfold lctArenaHi at harena_w; omega
  have hns_w : NODE_STRIDE < 2 ^ w := by
    have : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    dsimp only [arenaHi] at harena_w
    unfold lctArenaHi at harena_w; omega
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧ st.regs 4 = arenaHi ∧
    st.regs 5 = i ∧ i ≤ n ∧
    (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
    (∀ u ≤ cap, ∀ off < NODE_STRIDE,
      nodeField st.mem nb u off =
        if (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1
        else if (n + 1 ≤ u ∧ u ≤ n + i) ∧ off = OFF_EU then
          if u = cap then 0 else u + 1
        else 0)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 5) (lo := .const 0) (hi := .reg 0)
    (P := fun st => st.regs 0 = n ∧ st.regs 1 = b ∧ st.regs 2 = nb ∧ st.regs 3 = cap ∧
      st.regs 4 = arenaHi ∧ (∀ a < nb, st.mem a = memH a) ∧ (∀ a, arenaHi ≤ a → st.mem a = 0) ∧
      (∀ u ≤ cap, ∀ off < NODE_STRIDE,
        nodeField st.mem nb u off =
          if (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT) then 1 else 0))
    (Inv := Inv) 45 0 n (Nat.zero_le n) hw (fun _ => hn_w)
    (fun st ⟨hr0, hr1, hr2, hr3, hr4, hnb, har, hfl⟩ => by
      refine ⟨by simp [Expr.eval], hr0, hr1, hr2, hr3, hr4, by simp, Nat.zero_le n, ?_, ?_, ?_⟩
      · simpa using hnb
      · simpa using har
      · intro u hu off hoff
        have := hfl u hu off hoff
        dsimp only [nodeField] at this ⊢
        rw [this]
        split_ifs with h1 h2 h3
        · rfl
        · rfl
        · exfalso; omega
        · rfl)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h0 : st.regs 0 = n := hi.1
      simp [Expr.eval, h0])
    (fun i hi0 hin => by
      intro st ω ⟨hr0, hr1, hr2, hr3, hr4, hr5, _, hlt_nb, hge_ar, hfld⟩
      let ed := n + 1 + i
      have hed_le : ed ≤ cap := by unfold ed cap lctCap; omega
      have hptr_lt : nb + NODE_STRIDE * ed + OFF_EU < arenaHi := by
        dsimp only [arenaHi, cap]
        unfold lctArenaHi NODE_STRIDE OFF_EU
        have h1 : NODE_STRIDE * ed + 8 < NODE_STRIDE * (cap + 1) := by
          unfold NODE_STRIDE; nlinarith
        omega
      have hptr_w : nb + NODE_STRIDE * ed < 2 ^ w := by
        unfold OFF_EU at hptr_lt; exact lt_of_le_of_lt (by omega) harena_w
      have hst_w : NODE_STRIDE * ed < 2 ^ w := by omega
      have hed_w : ed < 2 ^ w := by
        have : ed ≤ NODE_STRIDE * ed := Nat.le_mul_of_pos_left _ (by unfold NODE_STRIDE; omega)
        omega
      have hn1_w : n + 1 < 2 ^ w := by omega
      have h1_w : 1 < 2 ^ w := hw
      have hi1_w : i + 1 < 2 ^ w := lt_of_le_of_lt hin hn_w
      have hed1_w : ed + 1 < 2 ^ w := by
        have hlt_c : ed + 1 ≤ cap + 1 := by omega
        have hle_a : cap + 1 ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_left _ (by unfold NODE_STRIDE; omega)
        dsimp only [arenaHi] at harena_w; unfold lctArenaHi at harena_w; omega
      let st1 := { st with regs := Function.update st.regs 6 ed }
      let st2 := { st1 with regs := Function.update st1.regs 7 (nb + NODE_STRIDE * ed) }
      let nextVal := if i + 1 = n then 0 else ed + 1
      let st3 := { st2 with mem := Function.update st2.mem (nb + NODE_STRIDE * ed + OFF_EU) nextVal }
      have hrun1 : Runs w p ω (Stmt.assign 6 (.bin .add (.bin .add (.reg 0) (.const 1)) (.reg 5)))
          st .normal st1 6 := by
        refine runs_assign_iff.mpr ⟨ed, ?_, rfl, rfl, rfl⟩
        simp [Expr.eval, hr0, hr5, h1_w, hn1_w, hed_w, ed]
      have hrun2 : Runs w p ω (Stmt.assign 7 (nodePtrExpr 2 6)) st1 .normal st2 6 := by
        refine runs_assign_iff.mpr ⟨nb + NODE_STRIDE * ed, ?_, rfl, rfl, rfl⟩
        simp [nodePtrExpr, Expr.eval, st1, Function.update_of_ne, Function.update_self,
          hr2, hns_w, hst_w, hptr_w]
      have hrun3 : Runs w p ω
          (Stmt.store (fieldAddrExpr 7 OFF_EU)
            (.bin .mul (.bin .sub (.const 1) (.bin .eq (.bin .add (.reg 5) (.const 1)) (.reg 0)))
              (.bin .add (.reg 6) (.const 1))))
          st2 .normal st3 15 := by
        refine runs_store_iff.mpr ⟨nb + NODE_STRIDE * ed + OFF_EU, nextVal, ?_, ?_, rfl, rfl, rfl⟩
        · have heu_w : OFF_EU < 2 ^ w := by
            unfold OFF_EU; exact lt_of_le_of_lt (by decide : 8 ≤ 30) (by simpa [NODE_STRIDE] using hns_w)
          have ha_w : nb + NODE_STRIDE * ed + OFF_EU < 2 ^ w := lt_trans hptr_lt harena_w
          simp [fieldAddrExpr, Expr.eval, st2, Function.update_self, heu_w, ha_w]
        · have hr5_2 : st2.regs 5 = i := by simp [st2, st1, Function.update_of_ne, hr5]
          have hr0_2 : st2.regs 0 = n := by simp [st2, st1, Function.update_of_ne, hr0]
          have hr6_2 : st2.regs 6 = ed := by simp [st2, st1, Function.update_of_ne, Function.update_self]
          by_cases hlast : i + 1 = n
          · simp [Expr.eval, hr5_2, hr0_2, hr6_2, h1_w, hn_w, hed1_w, nextVal, hlast,
              Nat.zero_lt_of_lt hw]
          · simp [Expr.eval, hr5_2, hr0_2, hr6_2, h1_w, hi1_w, hed1_w, nextVal, hlast,
              Nat.zero_lt_of_lt hw]
      have hseq := runs_seq_normal hrun1 (runs_seq_normal hrun2 hrun3)
      refine ⟨.normal, st3, _, hseq, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, by dsimp only; omega⟩
      · simpa [st3, st2, st1, Function.update_of_ne] using hr0
      · simpa [st3, st2, st1, Function.update_of_ne] using hr1
      · simpa [st3, st2, st1, Function.update_of_ne] using hr2
      · simpa [st3, st2, st1, Function.update_of_ne] using hr3
      · simpa [st3, st2, st1, Function.update_of_ne] using hr4
      · simp [st3, st2, st1]
      · omega
      · intro a ha
        have ha1 : a ≠ nb + NODE_STRIDE * ed + OFF_EU := by omega
        simpa [st3, st2, st1, Function.update_of_ne ha1] using hlt_nb a ha
      · intro a ha
        have ha1 : a ≠ nb + NODE_STRIDE * ed + OFF_EU := by omega
        simpa [st3, st2, st1, Function.update_of_ne ha1] using hge_ar a ha
      · intro u hu off hoff
        have haddr : nb + NODE_STRIDE * u + off = nb + NODE_STRIDE * ed + OFF_EU ↔
            u = ed ∧ off = OFF_EU :=
          ⟨addr_inj_stride hoff (by decide), by rintro ⟨rfl, rfl⟩; rfl⟩
        dsimp only [nodeField, st3, st2, st1]
        by_cases hue : u = ed ∧ off = OFF_EU
        · rcases hue with ⟨rfl, rfl⟩
          simp only [Function.update_self]
          have hnot_v : ¬ (1 ≤ ed ∧ ed ≤ n) := by unfold ed; omega
          have hle_e : ed ≤ n + (i + 1) := by unfold ed; omega
          have hedc : ed = cap ↔ i + 1 = n := by unfold ed cap lctCap; omega
          simp only [hnot_v, false_and, ↓reduceIte, hle_e, and_true, show n + 1 ≤ ed by unfold ed; omega]
          simp [nextVal, hedc]
        · rw [Function.update_of_ne (mt haddr.mp hue)]
          have hprev := hfld u hu off hoff
          dsimp only [nodeField] at hprev
          rw [hprev]
          have hiteT : ∀ {Q : Prop} [Decidable Q] {a b : ℕ}, Q → (if Q then a else b) = a := by
            intro Q _ a b hq; split_ifs; rfl
          have hiteF : ∀ {Q : Prop} [Decidable Q] {a b : ℕ}, ¬Q → (if Q then a else b) = b := by
            intro Q _ a b hnq; split_ifs; rfl
          by_cases h1 : (1 ≤ u ∧ u ≤ n) ∧ (off = OFF_ISV ∨ off = OFF_VCNT)
          · rw [hiteT h1, hiteT h1]
          · by_cases h2 : (n + 1 ≤ u ∧ u ≤ n + i) ∧ off = OFF_EU
            · have h3 : (n + 1 ≤ u ∧ u ≤ n + (i + 1)) ∧ off = OFF_EU := ⟨⟨h2.1.1, by omega⟩, h2.2⟩
              rw [hiteF h1, hiteF h1, hiteT h2, hiteT h3]
            · by_cases h3 : (n + 1 ≤ u ∧ u ≤ n + (i + 1)) ∧ off = OFF_EU
              · exfalso
                rcases (by dsimp only [ed]; omega : u ≤ n + i ∨ u = ed) with hle' | rfl
                · exact h2 ⟨⟨h3.1.1, hle'⟩, h3.2⟩
                · exact hue ⟨rfl, h3.2⟩
              · rw [hiteF h1, hiteF h1, hiteF h2, hiteF h3]
      · simpa [st3, st2, st1, Function.update_of_ne] using hr5)
  exact hloop.conseq (fun _ h => h)
    (fun o st => match o with
      | .normal => fun ⟨h0, h1, h2, h3, h4, _, _, hnb, har, hfl⟩ =>
          ⟨h0, h1, h2, h3, h4, hnb, har, by
            simpa [show n + n = cap by unfold cap lctCap; omega] using hfl⟩
      | .returned _ => False.elim)
    (fun _ _ => le_rfl)

/-- Running `lctInitBody L P` on `args = [n, b]` initializes an empty `n`-vertex `MathForest`
with `ZeroFrom` above `b + lctArenaWords n`, `lctPhi = 0`, and cost `≤ C_LCT_INIT * (n + 1)`. -/
theorem lctInit_runs {w h L P b n : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w) (hL : L < 2 ^ w) (hP : P < 2 ^ w)
    (hz₀ : ZeroFrom mem₀ b) (hb_w : b + lctArenaWords n < 2 ^ w) :
    ∀ ω, ∃ o st' c xInit,
      Runs w p ω (lctInitBody L P) (startState [n, b] mem₀ pos) o st' c ∧
      o.value = b + lctArenaWords n ∧
      LctMemRep w h L P b (MathForest.empty n) xInit st'.mem ∧
      (lctDSRep w h L P).Respects (fun _ => False) b (lctArenaWords n) mem₀ o.value b xInit st'.mem ∧
      c + lctPhi L st'.mem b n ≤ C_LCT_INIT * (n + 1) := by
  intro ω
  let nb := lctNodesBase b
  let cap := lctCap n
  let arenaHi := lctArenaHi b cap
  have hw4 : 4 ≤ w := by omega
  have h16_w : 16 ≤ 2 ^ w := by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hw4
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have harena_eq : arenaHi = b + lctArenaWords n := (lctArenaWords_eq b n).symm
  have harena_w : arenaHi < 2 ^ w := harena_eq ▸ hb_w
  have hnb_w : nb < 2 ^ w := by dsimp only [arenaHi, nb] at harena_w; unfold lctArenaHi at harena_w; omega
  have hcap_w : cap < 2 ^ w := by
    have : cap < NODE_STRIDE * (cap + 1) := by unfold NODE_STRIDE; omega
    dsimp only [arenaHi] at harena_w; unfold lctArenaHi at harena_w; omega
  have hn_w : n < 2 ^ w := by unfold cap lctCap at hcap_w; omega
  have hns_w : NODE_STRIDE < 2 ^ w := by
    have : NODE_STRIDE ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    dsimp only [arenaHi] at harena_w; unfold lctArenaHi at harena_w; omega
  have hfree_w : (if n = 0 then 0 else n + 1) < 2 ^ w := by
    split_ifs with hn0
    · exact Nat.zero_lt_of_lt hw1
    · have : n + 1 ≤ cap := by unfold cap lctCap; omega
      exact lt_of_le_of_lt this hcap_w
  let st0 := startState [n, b] mem₀ pos
  let r1 := Function.update st0.regs 2 nb
  let r2 := Function.update r1 3 cap
  let r3 := Function.update r2 4 arenaHi
  let mem1 := Function.update mem₀ (b + LCT_HDR_N) n
  let mem2 := Function.update mem1 (b + LCT_HDR_CAP) cap
  let mem3 := Function.update mem2 (b + LCT_HDR_FREE) (if n = 0 then 0 else n + 1)
  let mem4 := Function.update mem3 (b + LCT_HDR_L) L
  let mem5 := Function.update mem4 (b + LCT_HDR_P) P
  let mem6 := Function.update mem5 (b + LCT_HDR_HP) arenaHi
  have hhdr_w : ∀ k ≤ 5, b + k < 2 ^ w := fun k hk => by
    dsimp only [arenaHi] at harena_w; unfold lctArenaHi lctNodesBase LCT_HDR_SIZE at harena_w; omega
  have hrs_init : r3 0 = n ∧ r3 1 = b ∧ r3 2 = nb ∧ r3 3 = cap ∧ r3 4 = arenaHi := by
    have hr00 : st0.regs 0 = n := by simp [st0, startState]
    have hr01 : st0.regs 1 = b := by simp [st0, startState]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [r3, r2, r1, Function.update_of_ne, hr00, hr01]
  have hp1 : Runs w p ω (Stmt.assign 2 (.bin .add (.reg 1) (.const LCT_HDR_SIZE)))
      st0 .normal { st0 with regs := r1 } 4 := by
    refine runs_assign_iff.mpr ⟨nb, ?_, rfl, rfl, rfl⟩
    have hhdr_sz : LCT_HDR_SIZE < 2 ^ w := by unfold LCT_HDR_SIZE; omega
    have hnb_add : b + LCT_HDR_SIZE < 2 ^ w := by simpa [nb, lctNodesBase] using hnb_w
    simp [Expr.eval, st0, startState, hhdr_sz, hnb_add, nb, lctNodesBase]
  have hp2 : Runs w p ω (Stmt.assign 3 (.bin .mul (.const 2) (.reg 0)))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 4 := by
    refine runs_assign_iff.mpr ⟨cap, ?_, rfl, rfl, rfl⟩
    have hr0' : r1 0 = n := by simp [r1, st0, startState, Function.update_of_ne]
    simp [Expr.eval, hr0', hw2, show 2 * n < 2 ^ w by simpa [cap, lctCap] using hcap_w, cap, lctCap]
  have hp3 : Runs w p ω (Stmt.assign 4 (.bin .add (.reg 2)
      (.bin .mul (.const NODE_STRIDE) (.bin .add (.reg 3) (.const 1)))))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 8 := by
    refine runs_assign_iff.mpr ⟨arenaHi, ?_, rfl, rfl, rfl⟩
    have h2' : r2 2 = lctNodesBase b := by simp [r2, r1, Function.update_of_ne, nb]
    have h3' : r2 3 = cap := by simp [r2, Function.update_self]
    have hcap1_w : cap + 1 < 2 ^ w := by
      have : cap + 1 ≤ NODE_STRIDE * (cap + 1) := Nat.le_mul_of_pos_left _ (by unfold NODE_STRIDE; omega)
      dsimp only [arenaHi] at harena_w; unfold lctArenaHi at harena_w; omega
    have hmul_w : NODE_STRIDE * (cap + 1) < 2 ^ w := by
      dsimp only [arenaHi] at harena_w; unfold lctArenaHi at harena_w; omega
    have har_add : lctNodesBase b + NODE_STRIDE * (cap + 1) < 2 ^ w := by
      simpa [arenaHi, lctArenaHi] using harena_w
    simp [Expr.eval, h2', h3', hw1, hcap1_w, hns_w, hmul_w, har_add, arenaHi, lctArenaHi]
  have hp4 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_N)) (.reg 0))
      { st0 with regs := r3 } .normal { mem := mem1, regs := r3, pos := pos } 5 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_N, n, ?_, ?_, rfl, rfl, rfl⟩
    · have hb_lt_w : b < 2 ^ w := lt_trans (b_lt_lctArenaHi b cap) harena_w
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_N, Nat.zero_lt_of_lt hw1, hb_lt_w]
    · simp [Expr.eval, hrs_init.1]
  have hp5 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_CAP)) (.reg 3))
      { mem := mem1, regs := r3, pos := pos } .normal { mem := mem2, regs := r3, pos := pos } 5 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_CAP, cap, ?_, ?_, rfl, rfl, rfl⟩
    · have ha1 : b + 1 < 2 ^ w := hhdr_w 1 (by decide)
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_CAP, hw1, ha1]
    · simp [Expr.eval, hrs_init.2.2.2.1]
  have hp6 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_FREE))
      (.bin .mul (.bin .sub (.const 1) (.bin .eq (.reg 0) (.const 0)))
        (.bin .add (.reg 0) (.const 1))))
      { mem := mem2, regs := r3, pos := pos } .normal { mem := mem3, regs := r3, pos := pos } 13 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_FREE, (if n = 0 then 0 else n + 1), ?_, ?_, rfl, rfl, rfl⟩
    · have ha2 : b + 2 < 2 ^ w := hhdr_w 2 (by decide)
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_FREE, hw2, ha2]
    · by_cases hn0 : n = 0
      · simp [Expr.eval, hrs_init.1, hn0, hw1]
      · have hn1_w : n + 1 < 2 ^ w := by simpa [hn0] using hfree_w
        simp [Expr.eval, hrs_init.1, hn0, hw1, hn1_w]
  have hp7 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_L)) (.const L))
      { mem := mem3, regs := r3, pos := pos } .normal { mem := mem4, regs := r3, pos := pos } 5 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_L, L, ?_, ?_, rfl, rfl, rfl⟩
    · have h3w : 3 < 2 ^ w := by omega
      have ha3 : b + 3 < 2 ^ w := hhdr_w 3 (by decide)
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_L, h3w, ha3]
    · simp [Expr.eval, hL]
  have hp8 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_P)) (.const P))
      { mem := mem4, regs := r3, pos := pos } .normal { mem := mem5, regs := r3, pos := pos } 5 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_P, P, ?_, ?_, rfl, rfl, rfl⟩
    · have h4w : 4 < 2 ^ w := by omega
      have ha4 : b + 4 < 2 ^ w := hhdr_w 4 (by decide)
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_P, h4w, ha4]
    · simp [Expr.eval, hP]
  have hp9 : Runs w p ω (Stmt.store (.bin .add (.reg 1) (.const LCT_HDR_HP)) (.reg 4))
      { mem := mem5, regs := r3, pos := pos } .normal { mem := mem6, regs := r3, pos := pos } 5 := by
    refine runs_store_iff.mpr ⟨b + LCT_HDR_HP, arenaHi, ?_, ?_, rfl, rfl, rfl⟩
    · have h5w : 5 < 2 ^ w := by omega
      have ha5 : b + 5 < 2 ^ w := hhdr_w 5 (by decide)
      simp [Expr.eval, hrs_init.2.1, LCT_HDR_HP, h5w, ha5]
    · simp [Expr.eval, hrs_init.2.2.2.2]
  have hl1 := lctInit_loop1_triple (L := L) (P := P) p mem₀ hw1 hb_w hz₀
  rcases hl1 { mem := mem6, regs := r3, pos := pos } ω
    ⟨rfl, hrs_init.1, hrs_init.2.1, hrs_init.2.2.1, hrs_init.2.2.2.1, hrs_init.2.2.2.2⟩ with
    ⟨o1, st_mid, c_l1, hr_l1, hpost_l1, hc_l1⟩
  cases o1 with
  | returned _ => exact False.elim hpost_l1
  | normal =>
      dsimp only [normalPost] at hpost_l1
      have hl2 := lctInit_loop2_triple p hw1 hb_w mem6
      rcases hl2 st_mid ω hpost_l1 with ⟨o2, st_end, c_l2, hr_l2, hpost_l2, hc_l2⟩
      cases o2 with
      | returned _ => exact False.elim hpost_l2
      | normal =>
          dsimp only [normalPost] at hpost_l2
          rcases hpost_l2 with ⟨he0, he1, he2, he3, he4, he_nb, he_ar, he_fld⟩
          have hret : Runs w p ω (Stmt.ret (.reg 4)) st_end (.returned arenaHi) st_end 2 := by
            refine runs_ret_iff.mpr ⟨arenaHi, ?_, rfl, rfl, rfl⟩
            simp [Expr.eval, he4]; rfl
          have hfull : Runs w p ω (lctInitBody L P) st0 (.returned arenaHi) st_end _ :=
            runs_seq_normal hp1 (runs_seq_normal hp2 (runs_seq_normal hp3 (runs_seq_normal hp4
              (runs_seq_normal hp5 (runs_seq_normal hp6 (runs_seq_normal hp7 (runs_seq_normal hp8
                (runs_seq_normal hp9 (runs_seq_normal hr_l1 (runs_seq_normal hr_l2 hret))))))))))
          let xInit := lctInitConc b n
          have hzero_off : ∀ u ≤ cap, ∀ off < NODE_STRIDE,
              off ≠ OFF_ISV → off ≠ OFF_VCNT → off ≠ OFF_EU →
              nodeField st_end.mem nb u off = 0 := fun u hu off hoff h1 h2 h3 => by
            rw [he_fld u hu off hoff]; split_ifs <;> simp_all
          have hzch : ∀ u, 1 ≤ u → u ≤ cap →
              nodeField st_end.mem nb u OFF_LEFT = 0 ∧
              nodeField st_end.mem nb u OFF_RIGHT = 0 ∧
              nodeField st_end.mem nb u OFF_PPAR = 0 := fun u hu1 hu2 =>
            ⟨hzero_off u hu2 OFF_LEFT (by decide) (by decide) (by decide) (by decide),
             hzero_off u hu2 OFF_RIGHT (by decide) (by decide) (by decide) (by decide),
             hzero_off u hu2 OFF_PPAR (by decide) (by decide) (by decide) (by decide)⟩
          have hphi0 : lctPhi L st_end.mem b n = 0 := init_phi_zero hzch
          have hhdr_read : ∀ k ≤ 5, st_end.mem (b + k) = mem6 (b + k) := fun k hk =>
            he_nb (b + k) (by unfold lctNodesBase LCT_HDR_SIZE; omega)
          have hm6_lt : ∀ a < b, mem6 a = mem₀ a := fun a ha => by
            dsimp only [mem6, mem5, mem4, mem3, mem2, mem1]
            unfold LCT_HDR_N LCT_HDR_CAP LCT_HDR_FREE LCT_HDR_L LCT_HDR_P LCT_HDR_HP
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          have hm6_vals :
              mem6 (b + LCT_HDR_N) = n ∧ mem6 (b + LCT_HDR_CAP) = cap ∧
              mem6 (b + LCT_HDR_FREE) = (if n = 0 then 0 else n + 1) ∧
              mem6 (b + LCT_HDR_L) = L ∧ mem6 (b + LCT_HDR_P) = P ∧
              mem6 (b + LCT_HDR_HP) = arenaHi := by
            dsimp only [mem6, mem5, mem4, mem3, mem2, mem1]
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
              simp [LCT_HDR_N, LCT_HDR_CAP, LCT_HDR_FREE, LCT_HDR_L, LCT_HDR_P, LCT_HDR_HP,
                Function.update_of_ne]
          have hfree_chain : FreeSlotChain st_end.mem nb (st_end.mem (b + LCT_HDR_FREE)) xInit.freeEdges := by
            rw [show b + LCT_HDR_FREE = b + 2 by unfold LCT_HDR_FREE; rfl, hhdr_read 2 (by decide)]
            rw [show b + 2 = b + LCT_HDR_FREE by unfold LCT_HDR_FREE; rfl, hm6_vals.2.2.1]
            have hnx : ∀ i < n, nodeField st_end.mem nb (n + 1 + i) OFF_EU =
                if i + 1 = n then 0 else n + 1 + (i + 1) := fun i hi => by
              rw [he_fld (n + 1 + i) (by unfold lctCap; omega) OFF_EU (by decide)]
              have hnotv : ¬ (1 ≤ n + 1 + i ∧ n + 1 + i ≤ n) := by omega
              have hn1 : n + 1 ≤ n + 1 + i := by omega
              have hic : n + 1 + i ≤ lctCap n := by unfold lctCap; omega
              have hlast : n + 1 + i = lctCap n ↔ i + 1 = n := by unfold lctCap; omega
              simp only [hnotv, false_and, ↓reduceIte, hn1, hic, and_self, hlast]
              split_ifs <;> omega
            simpa [xInit, lctInitConc] using freeSlotChain_init hnx n 0 (Nat.add_zero n)
          have hperm_nodes := initTrees_perm_nodes cap
          have htrees_ok : ∀ t ∈ xInit.trees, t ≠ .leaf ∧ nodeField st_end.mem nb t.rootId OFF_PPAR < 2 ^ w ∧
              TreeMemMatch w h L st_end.mem nb cap t 0 (nodeField st_end.mem nb t.rootId OFF_PPAR) := by
            intro t ht
            simp only [xInit, lctInitConc, List.mem_map, List.mem_range] at ht
            rcases ht with ⟨i, hi, rfl⟩
            have hi1 : 1 ≤ i + 1 := by omega
            have hi2 : i + 1 ≤ cap := by omega
            have hf_eq : ∀ off < NODE_STRIDE, off ≠ OFF_ISV → off ≠ OFF_VCNT → off ≠ OFF_EU →
                nodeField st_end.mem nb (i + 1) off = 0 := hzero_off (i + 1) hi2
            have hisv_1 : i + 1 ≤ n → nodeField st_end.mem nb (i + 1) OFF_ISV = 1 ∧
                nodeField st_end.mem nb (i + 1) OFF_VCNT = 1 := fun hin => by
              rw [he_fld (i + 1) hi2 OFF_ISV (by decide), he_fld (i + 1) hi2 OFF_VCNT (by decide)]
              simp [hi1, hin]
            have hisv_0 : n + 1 ≤ i + 1 → nodeField st_end.mem nb (i + 1) OFF_ISV = 0 ∧
                nodeField st_end.mem nb (i + 1) OFF_VCNT = 0 := fun hin => by
              rw [he_fld (i + 1) hi2 OFF_ISV (by decide), he_fld (i + 1) hi2 OFF_VCNT (by decide)]
              simp [show ¬(i + 1 ≤ n) by omega, show OFF_ISV ≠ OFF_EU by decide,
                show OFF_VCNT ≠ OFF_EU by decide]
            have hpp0 : nodeField st_end.mem nb (i + 1) OFF_PPAR = 0 :=
              hf_eq OFF_PPAR (by decide) (by decide) (by decide) (by decide)
            refine ⟨by simp, by dsimp only [AuxTree.rootId]; rw [hpp0]; exact Nat.zero_lt_of_lt hw1, ?_⟩
            dsimp only [AuxTree.rootId]; rw [hpp0]
            refine ⟨hi1, hi2, ?_, ?_, ?_, hpp0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
              ?_, ?_, Or.inl (hf_eq OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide)),
              Or.inl (hf_eq OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide)),
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial, trivial⟩
            · exact hf_eq OFF_LEFT (by decide) (by decide) (by decide) (by decide)
            · exact hf_eq OFF_RIGHT (by decide) (by decide) (by decide) (by decide)
            · exact hf_eq OFF_PARENT (by decide) (by decide) (by decide) (by decide)
            · rw [hf_eq OFF_REV (by decide) (by decide) (by decide) (by decide)]; omega
            · by_cases hin : i + 1 ≤ n <;> [rw [(hisv_1 hin).1]; rw [(hisv_0 hin).1]] ; omega
            · rw [hf_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)]; omega
            · by_cases hin : i + 1 ≤ n
              · rw [(hisv_1 hin).1, hf_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)]; try omega
              · rw [(hisv_0 (by omega)).1, hf_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)]; omega
            · rw [hf_eq OFF_DIR (by decide) (by decide) (by decide) (by decide)]; omega
            · rw [hf_eq OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide)]; omega
            · rw [hf_eq OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide)]; omega
            · rw [he_fld (i + 1) hi2 OFF_EU (by decide)]
              split_ifs <;> first
                | exact hw1
                | exact Nat.zero_lt_of_lt hw1
                | exact lt_of_le_of_lt (by omega : i + 1 + 1 ≤ cap) hcap_w
            · rw [hf_eq OFF_EV (by decide) (by decide) (by decide) (by decide)]; exact Nat.zero_lt_of_lt hw1
            · rw [hf_eq OFF_EID (by decide) (by decide) (by decide) (by decide)]; exact Nat.zero_lt_of_lt hw1
            · intro h1; rw [hf_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)] at h1; omega
            · intro _
              refine ⟨hf_eq OFF_DIR (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_FLOW_PTR (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_AF_PTR (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_AB_PTR (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_COST_FWD (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_COST_BWD (by decide) (by decide) (by decide) (by decide)⟩
            · intro h1; rw [hf_eq OFF_HAS_TAG (by decide) (by decide) (by decide) (by decide)] at h1; omega
            · intro _
              exact ⟨hf_eq OFF_TAG_PTR (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_TAG_NEG (by decide) (by decide) (by decide) (by decide)⟩
            · rw [hf_eq OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)]; omega
            · rw [hf_eq OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide)]
            · intro h1; rw [hf_eq OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)] at h1; omega
            · intro _
              exact ⟨hf_eq OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide),
                hf_eq OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide)⟩
            · have hrev0 : revFlag st_end.mem nb (i + 1) = false := by
                simp [revFlag, hf_eq OFF_REV (by decide) (by decide) (by decide) (by decide)]
              have hown0 : nodeOwnRawStep st_end.mem nb h L (i + 1) = none := by
                simp [nodeOwnRawStep, hf_eq OFF_HASE (by decide) (by decide) (by decide) (by decide)]
              have hsteps : evalMemSteps st_end.mem nb h L (.node (i + 1) .leaf .leaf) false 0 = [] := by
                simp [evalMemSteps, hown0]
              have hvc : nodeField st_end.mem nb (i + 1) OFF_VCNT =
                  listVcnt st_end.mem nb ((AuxTree.node (i + 1) .leaf .leaf).evalInorder (revFlag st_end.mem nb) false) := by
                simp only [AuxTree.evalInorder, listVcnt, List.nil_append, List.append_nil, Nat.add_zero]
                by_cases hin : i + 1 ≤ n
                · rw [(hisv_1 hin).2, (hisv_1 hin).1]
                · rw [(hisv_0 (by omega)).2, (hisv_0 (by omega)).1]
              have hm10 : nodeIntMinAgg1 st_end.mem nb h L (i + 1) = ⟨false, 0, 0, 0⟩ := by
                simp [nodeIntMinAgg1, hf_eq OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN1_VAL (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN1_FIRST (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN1_LAST (by decide) (by decide) (by decide) (by decide), optIntVal]
              have hm20 : nodeIntMinAgg2 st_end.mem nb h L (i + 1) = ⟨false, 0, 0, 0⟩ := by
                simp [nodeIntMinAgg2, hf_eq OFF_MIN2_HAS (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN2_VAL (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN2_FIRST (by decide) (by decide) (by decide) (by decide),
                  hf_eq OFF_MIN2_LAST (by decide) (by decide) (by decide) (by decide), optIntVal]
              refine ⟨hvc, ?_, ?_, ?_, ?_, ?_⟩
              · rw [hsteps]
                simp [optIntVal, hf_eq OFF_CSUM_FWD (by decide) (by decide) (by decide) (by decide),
                  listRawCost, wrap_of_fits (fits_zero h L)]
              · rw [hsteps]
                simp [optIntVal, hf_eq OFF_CSUM_BWD (by decide) (by decide) (by decide) (by decide),
                  listRawCost, wrap_of_fits (fits_zero h L)]
              · rw [hsteps, hf_eq OFF_MIN1_HAS (by decide) (by decide) (by decide) (by decide)]; simp
              · rw [hsteps]; simpa [listIntMinAgg] using hm10
              · rw [hsteps]; simpa [listIntMinAgg] using hm20
          have hs0 : SlotZeroOk st_end.mem nb := fun off hoff => by
            rw [show st_end.mem (nb + off) = nodeField st_end.mem nb 0 off by simp [nodeField]]
            rw [he_fld 0 (Nat.zero_le _) off hoff]; simp
          have hsf : SplayForestOk w h L st_end.mem nb cap xInit.trees := by
            refine ⟨hh, hw, lctNodesBase_ge3 b, ?_, ?_, ?_, ?_, hs0, hperm_nodes, htrees_ok⟩
            · rw [show nb - 1 = b + 5 by unfold nb lctNodesBase LCT_HDR_SIZE; omega, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact le_rfl
            · rw [show nb - 3 = b + 3 by unfold nb lctNodesBase LCT_HDR_SIZE; omega, hhdr_read 3 (by decide)]
              exact hm6_vals.2.2.2.1
            · rw [show nb - 1 = b + 5 by unfold nb lctNodesBase LCT_HDR_SIZE; omega, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact harena_w
            · rw [show nb - 1 = b + 5 by unfold nb lctNodesBase LCT_HDR_SIZE; omega, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact he_ar
          have hrep : LctMemRep w h L P b (MathForest.empty n) xInit st_end.mem := by
            refine ⟨hh, hw, MathForest.empty_valid n, fun e he => by simp [MathForest.empty] at he,
              rfl, le_rfl, ?_,
              lctFoot_arena
                (by dsimp only [xInit, lctInitConc]; have := b_lt_lctArenaHi b (lctCap n); omega)
                (by dsimp only [xInit, lctInitConc, MathForest.empty]; have := b_lt_lctArenaHi b (lctCap n); omega),
              fun iv hiv => by simp [xInit, lctInitConc] at hiv,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfree_chain, ?_, hs0, hperm_nodes, htrees_ok, ?_, ?_, ?_, ?_, ?_⟩
            · exact lt_of_le_of_lt (Nat.zero_le _) (b_lt_lctArenaHi b cap)
            · rw [show b + LCT_HDR_N = b + 0 by unfold LCT_HDR_N; rfl, hhdr_read 0 (by decide)]
              exact hm6_vals.1
            · rw [show b + LCT_HDR_CAP = b + 1 by unfold LCT_HDR_CAP; rfl, hhdr_read 1 (by decide)]
              exact hm6_vals.2.1
            · rw [show b + LCT_HDR_L = b + 3 by unfold LCT_HDR_L; rfl, hhdr_read 3 (by decide)]
              exact hm6_vals.2.2.2.1
            · rw [show b + LCT_HDR_P = b + 4 by unfold LCT_HDR_P; rfl, hhdr_read 4 (by decide)]
              exact hm6_vals.2.2.2.2.1
            · rw [show b + LCT_HDR_HP = b + 5 by unfold LCT_HDR_HP; rfl, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact le_rfl
            · rw [show b + LCT_HDR_HP = b + 5 by unfold LCT_HDR_HP; rfl, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact le_rfl
            · rw [show b + LCT_HDR_HP = b + 5 by unfold LCT_HDR_HP; rfl, hhdr_read 5 (by decide)]
              rw [show b + 5 = b + LCT_HDR_HP by rfl, hm6_vals.2.2.2.2.2]; exact harena_w
            · simp [xInit, lctInitConc, MathForest.empty]
            · simp [xInit, lctInitConc, MathForest.empty]
            · intro ed hed
              simp only [xInit, lctInitConc, List.mem_map, List.mem_range] at hed
              rcases hed with ⟨i, hi, rfl⟩
              have hi_n : i < n := hi
              have hic : n + 1 + i ≤ lctCap n := by unfold lctCap; omega
              refine ⟨by dsimp only [MathForest.empty]; omega, hic, ?_, ?_, ?_, ?_⟩
              · simp only [xInit, lctInitConc, List.mem_map, List.mem_range]
                exact ⟨i + n, by unfold lctCap; omega, by congr 1; omega⟩
              · exact hzero_off (n + 1 + i) hic OFF_PPAR (by decide) (by decide) (by decide) (by decide)
              · rw [he_fld (n + 1 + i) hic OFF_ISV (by decide)]
                simp [show ¬(1 ≤ n + 1 + i ∧ n + 1 + i ≤ n) by omega, show OFF_ISV ≠ OFF_EU by decide]
              · exact hzero_off (n + 1 + i) hic OFF_HASE (by decide) (by decide) (by decide) (by decide)
            · intro v hv
              have hv_n : v < n := hv
              have hv1 : v + 1 ≤ lctCap n := by unfold lctCap; omega
              dsimp only
              rw [he_fld (v + 1) hv1 OFF_ISV (by decide),
                hzero_off (v + 1) hv1 OFF_HASE (by decide) (by decide) (by decide) (by decide)]
              simp [hv_n, show 1 ≤ v + 1 by omega]
            · intro pr hpr; simp [xInit, lctInitConc] at hpr
            · intro t ht
              simp only [xInit, lctInitConc, List.mem_map, List.mem_range] at ht
              rcases ht with ⟨i, hi, rfl⟩
              have hi_c : i < lctCap n := hi
              have hic : i + 1 ≤ lctCap n := by omega
              have hpp0 : nodeField st_end.mem nb (i + 1) OFF_PPAR = 0 :=
                hzero_off (i + 1) hic OFF_PPAR (by decide) (by decide) (by decide) (by decide)
              refine ⟨?_, Or.inl hpp0, ?_⟩
              · simp [AuxTree.evalInorder]
              · by_cases hin : i < n
                · right; refine ⟨i, hin, ?_⟩; simp [AuxTree.evalInorder]
                · left; refine ⟨?_, rfl, hpp0⟩
                  dsimp only [AuxTree.rootId]
                  simp only [xInit, lctInitConc, List.mem_map, List.mem_range]
                  exact ⟨i - n, by unfold lctCap at hi_c; omega, by omega⟩
            · have hpar0 : ∀ u, lctAuxParent st_end.mem nb (lctCap n) u = 0 := by
                intro u
                unfold lctAuxParent
                cases hfnd : (auxRootIds st_end.mem nb (lctCap n)).findSome?
                    (fun r => treeParentEntry st_end.mem nb (lctCap n) r u) with
                | none => rfl
                | some pval =>
                    rcases List.findSome?_eq_some_iff.1 hfnd with ⟨_, r, _, hlist, hpe, _⟩
                    have hr_mem : r ∈ auxRootIds st_end.mem nb (lctCap n) := by rw [hlist]; simp
                    simp only [auxRootIds, List.mem_filter, List.mem_map, List.mem_range] at hr_mem
                    rcases hr_mem with ⟨⟨j, hj, rfl⟩, _⟩
                    have hj1 : j + 1 ≤ lctCap n := by omega
                    have hr_tree : AuxTree.node (j + 1) .leaf .leaf ∈ xInit.trees := by
                      simp [xInit, lctInitConc]; exact hj
                    have hseq := SplayForestOk.lctTreeSeq_eq hsf hr_tree
                    dsimp only [cap, AuxTree.rootId] at hseq
                    have hseq_eq : lctTreeSeq st_end.mem nb (lctCap n) (j + 1) = [j + 1] := by
                      rw [hseq]; simp [AuxTree.evalInorder]
                    have hpp0 : nodeField st_end.mem nb (j + 1) OFF_PPAR = 0 :=
                      hzero_off (j + 1) hj1 OFF_PPAR (by decide) (by decide) (by decide) (by decide)
                    dsimp only [treeParentEntry] at hpe
                    rw [hseq_eq, hpp0] at hpe
                    simp only [Nat.zero_le, ↓reduceIte] at hpe
                    split_ifs at hpe with hu_eq
                    cases hpe
                    simp at hu_eq; subst hu_eq
                    simp [listParentFrom]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro u hu1 hu2
                dsimp only [MathForest.empty] at hu2 ⊢
                cases hcap : lctCap n with
                | zero => omega
                | succ k =>
                    rw [iterParent, ← hcap, hpar0 u]
                    exact iterParent_zero_fixed (hpar0 0) k
              · intro ed hed
                simp only [xInit, lctInitConc, List.mem_map, List.mem_range] at hed
                rcases hed with ⟨i, hi, rfl⟩
                exact hpar0 (n + 1 + i)
              · intro v hv
                exact Or.inl (hpar0 (v + 1))
              · intro pr hpr; simp [xInit, lctInitConc] at hpr
            · intro u hu off hoff
              left
              have hnp : off ∉ [OFF_ISV, OFF_VCNT, OFF_EU] := by
                rcases (by simpa [ptrOffs] using hoff :
                  off = OFF_FLOW_PTR ∨ off = OFF_AF_PTR ∨ off = OFF_AB_PTR ∨ off = OFF_COST_FWD ∨
                  off = OFF_COST_BWD ∨ off = OFF_CSUM_FWD ∨ off = OFF_CSUM_BWD ∨ off = OFF_TAG_PTR ∨
                  off = OFF_MIN1_VAL ∨ off = OFF_MIN2_VAL) with
                  rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
              exact hzero_off u hu off (ptrOffs_lt_stride hoff)
                (by intro h; apply hnp; simp [h])
                (by intro h; apply hnp; simp [h])
                (by intro h; apply hnp; simp [h])
          have hresp : (lctDSRep w h L P).Respects (fun _ => False) b (lctArenaWords n)
              mem₀ arenaHi b xInit st_end.mem := by
            refine ⟨le_trans (le_of_lt (b_lt_lctArenaHi b cap)) le_rfl, ?_, ?_, ?_, ?_⟩
            · rw [harena_eq]
            · exact fun a ha => he_ar a ha
            · intro a ha _
              rw [he_nb a (by unfold lctNodesBase LCT_HDR_SIZE; omega)]
              exact hm6_lt a ha
            · intro a ha
              simp only [lctDSRep, lctFoot, xInit, lctInitConc, List.not_mem_nil, false_and,
                exists_false, or_false] at ha
              exact Or.inr ha
          refine ⟨.returned arenaHi, st_end, _, xInit, hfull, ?_, hrep, hresp, ?_⟩
          · simp [Outcome.value, arenaHi, harena_eq]
          · rw [hphi0, Nat.add_zero]
            unfold C_LCT_INIT
            simp only [Expr.size] at hc_l1 hc_l2
            omega

end InitProcedure

end MinCostFlow.LinkCut.Prog
