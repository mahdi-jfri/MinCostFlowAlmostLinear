module

public import MinCostFlow.DynSpanner.Program.GraphTranslateRev

/-!
# Reverse Graph Translation: Walk Decoding (`gtDecodeWalks_meetsContract`)

Verifies `gtDecodeWalksStmt` (`gtIdxDecodeWalks = 1` in `gtRevPrimProcs`) against
`gtDecodeWalksContract` by factoring out the inner edge-decoding loop (`gtDecodeInnerBody_triple`,
`gtDecodeInnerLoop_triple`) from the outer walk loop.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner

@[expose] public section

private def gtDecodeInnerBody : Stmt :=
  .assign 18 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 17)))) ;;
  .assign 19 (.load (.bin .add (.reg 13) (.bin .add (.const 2) (.reg 17)))) ;;
  .assign 20 (.load (.bin .add (.reg 13) (.bin .add (.bin .add (.const 2) (.reg 14)) (.reg 17)))) ;;
  .assign 21 (.bin .mul (.const 2) (.reg 20)) ;;
  .assign 22 (.load (.bin .add (.reg 8) (.reg 21))) ;;
  .assign 23 (.load (.bin .add (.reg 8) (.bin .add (.reg 21) (.const 1)))) ;;
  .assign 24 (.bin .mul (.bin .eq (.reg 22) (.reg 18)) (.bin .eq (.reg 23) (.reg 19))) ;;
  .assign 25 (.load (.bin .add (.reg 9) (.reg 20))) ;;
  .assign 26 (.load (.bin .add (.reg 1) (.reg 25))) ;;
  .assign 27 (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 17)))) ;;
  .store (.reg 27) (.reg 26) ;;
  .store (.bin .add (.reg 27) (.const 1)) (.reg 24)

private def gtDecodeInnerInv (w0 : ℕ) (dWalk : List (ℕ × Bool))
    (mem2 : ℕ → ℕ) (stSteps : State) (k : ℕ) (s' : State) : Prop :=
  (∀ r ≤ 16, s'.regs r = stSteps.regs r) ∧
  s'.regs 17 = k ∧
  s'.mem w0 = dWalk.length ∧
  (∀ t (_ : t < k), ∃ htp : t < dWalk.length,
    s'.mem (w0 + 1 + 2 * t) = (dWalk[t]'htp).1 ∧
    s'.mem (w0 + 1 + 2 * t + 1) = (if (dWalk[t]'htp).2 then 1 else 0)) ∧
  ∀ addr, addr < w0 + 1 ∨ w0 + 1 + 2 * k ≤ addr → s'.mem addr = mem2 addr

private lemma gtDecodeInnerBody_triple {w : ℕ} {p : Program}
    {jEs kept : List ℕ} {cJtilde : Cited.Graph} {P : Walk}
    {mem mem2 : ℕ → ℕ} {stSteps : State} {dis : ℕ → Prop}
    {jEsPtr guestBase jtildeG keptG w0 wAddr k : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (heCap : ∀ idx ∈ jEs, idx < 2 ^ w)
    (hkept_lt : ∀ x ∈ kept, x < jEs.length)
    (hP_info : P.verts.length < 2 ^ w ∧ P.edges.length < 2 ^ w ∧
      wAddr + P.encode.length < 2 ^ w ∧
      (∀ c ∈ P.edges, c < cJtilde.m ∧ c < kept.length) ∧
      ∀ u ∈ P.verts, u < 2 ^ w)
    (hcJB : guestBase + jtildeG + cJtilde.encode.length < 2 ^ w)
    (hkeptB : guestBase + keptG + 1 + kept.length < 2 ^ w)
    (hjEB : jEsPtr + jEs.length < 2 ^ w)
    (hw_bound : w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) < 2 ^ w)
    (hcJ_w : ∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w)
    (hjE_at : ListAt mem jEsPtr jEs)
    (hcJ_at : GraphAt mem (guestBase + jtildeG) cJtilde)
    (hkept_at : ListAt mem (guestBase + keptG) (kept.length :: kept))
    (hwAddr_at : WalkAt mem wAddr P)
    (hAgree : ∀ {addr}, dis addr → mem2 addr = mem addr)
    (hDisjOut : ∀ {addr}, dis addr →
      addr < w0 ∨ w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) ≤ addr)
    (hDisjJE : ∀ i < jEs.length, dis (jEsPtr + i))
    (hDisjCJ : ∀ i < cJtilde.encode.length, dis (guestBase + jtildeG + i))
    (hDisjKept : ∀ i < 1 + kept.length, dis (guestBase + keptG + i))
    (hDisjWalk : ∀ i < P.encode.length, dis (wAddr + i))
    (hr_u0 : stSteps.regs 13 = wAddr)
    (hr_14_0 : stSteps.regs 14 = P.verts.length)
    (hr_8_0 : stSteps.regs 8 = guestBase + jtildeG + 2)
    (hr_9_0 : stSteps.regs 9 = guestBase + keptG + 1)
    (hr_1_0 : stSteps.regs 1 = jEsPtr)
    (hr_7_0 : stSteps.regs 7 = w0)
    (hk_lt : k < (citedWalkSteps jEs cJtilde kept P.verts P.edges).length) :
    Triple w p
      (gtDecodeInnerInv w0 (citedWalkSteps jEs cJtilde kept P.verts P.edges) mem2 stSteps k)
      gtDecodeInnerBody
      (normalPost fun st₁ =>
        gtDecodeInnerInv w0 (citedWalkSteps jEs cJtilde kept P.verts P.edges) mem2 stSteps (k + 1)
          { st₁ with regs := Function.update st₁.regs 17 (k + 1) } ∧
        st₁.regs 17 = k)
      (fun _ => 150) := by
  intro stK ω'' ⟨hregsK, hr17, hmK_w0, hcellsK, hfrK⟩
  let dWalk := citedWalkSteps jEs cJtilde kept P.verts P.edges
  have hdWalk_len : dWalk.length = min (P.verts.length - 1) P.edges.length :=
    citedWalkSteps_length jEs cJtilde kept P.verts P.edges
  have hk_le : k < min (P.verts.length - 1) P.edges.length := by rwa [← hdWalk_len]
  have hk_v : k < P.verts.length := by omega
  have hk1_v : k + 1 < P.verts.length := by omega
  have hk_e : k < P.edges.length := by omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  set u := P.verts[k]'hk_v
  set v := P.verts[k + 1]'hk1_v
  set c := P.edges[k]'hk_e
  have hc_mem : c ∈ P.edges := List.getElem_mem hk_e
  have hc_info := hP_info.2.2.2.1 c hc_mem
  have hc_lt_m : c < cJtilde.m := hc_info.1
  have hc_lt_kept : c < kept.length := hc_info.2
  have hkc_lt_jEs : kept[c]'hc_lt_kept < jEs.length := hkept_lt _ (List.getElem_mem hc_lt_kept)
  set kept_c := kept[c]'hc_lt_kept
  set eStep := jEs[kept_c]'hkc_lt_jEs
  set eG := cJtilde.edges[c]'hc_lt_m
  have heStep_w : eStep < 2 ^ w := heCap eStep (List.getElem_mem hkc_lt_jEs)
  have hu_ltw : u < 2 ^ w := hP_info.2.2.2.2 u (List.getElem_mem hk_v)
  have hv_ltw : v < 2 ^ w := hP_info.2.2.2.2 v (List.getElem_mem hk1_v)
  have hwAddr_ltw : wAddr + P.encode.length < 2 ^ w := hP_info.2.2.1
  have hcJ_len : cJtilde.encode.length = 2 + 2 * cJtilde.m := graph_encode_length cJtilde
  have hP_len : P.encode.length = 2 + P.verts.length + P.edges.length := walk_encode_length P
  have hc_ltw : c < 2 ^ w := by omega
  have h2c_ltw : 2 * c < 2 ^ w := by omega
  have hkept_c_ltw : kept_c < 2 ^ w := by omega
  have heG_w := hcJ_w c hc_lt_m
  rw [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem (show c < cJtilde.edges.length from hc_lt_m),
    Option.getD_some] at heG_w
  have hr_u : stK.regs 13 = wAddr := by rw [hregsK 13 (by decide), hr_u0]
  have hr_14 : stK.regs 14 = P.verts.length := by rw [hregsK 14 (by decide), hr_14_0]
  have hr_8 : stK.regs 8 = guestBase + jtildeG + 2 := by rw [hregsK 8 (by decide), hr_8_0]
  have hr_9 : stK.regs 9 = guestBase + keptG + 1 := by rw [hregsK 9 (by decide), hr_9_0]
  have hr_1 : stK.regs 1 = jEsPtr := by rw [hregsK 1 (by decide), hr_1_0]
  have hr_7 : stK.regs 7 = w0 := by rw [hregsK 7 (by decide), hr_7_0]
  have hmem_back : ∀ {addr}, dis addr → stK.mem addr = mem addr := by
    intro addr hd
    have hdwk : addr < w0 + 1 ∨ w0 + 1 + 2 * k ≤ addr := by
      rcases hDisjOut hd with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    rw [hfrK addr hdwk, hAgree hd]
  have hm_u : stK.mem (wAddr + (1 + k)) = u := by
    rw [hmem_back (hDisjWalk (1 + k) (by omega))]
    simpa [Nat.add_assoc] using hwAddr_at.verts_listAt k hk_v
  have hm_v : stK.mem (wAddr + (2 + k)) = v := by
    rw [hmem_back (hDisjWalk (2 + k) (by omega)), show 2 + k = 1 + (k + 1) by omega]
    simpa [Nat.add_assoc] using hwAddr_at.verts_listAt (k + 1) hk1_v
  have hm_c : stK.mem (wAddr + (2 + P.verts.length + k)) = c := by
    rw [hmem_back (hDisjWalk (2 + P.verts.length + k) (by omega))]
    simpa [Nat.add_assoc] using hwAddr_at.edges_listAt k hk_e
  have hm_eG1 : stK.mem ((guestBase + jtildeG + 2) + 2 * c) = eG.1 := by
    have hd := hDisjCJ (2 + 2 * c) (by omega)
    rw [hmem_back (by simpa [Nat.add_assoc] using hd)]
    simpa [Nat.add_assoc] using graphAt_edge_fst hcJ_at hc_lt_m
  have hm_eG2 : stK.mem ((guestBase + jtildeG + 2) + (2 * c + 1)) = eG.2 := by
    have hd := hDisjCJ (3 + 2 * c) (by omega)
    rw [show guestBase + jtildeG + (3 + 2 * c) = (guestBase + jtildeG + 2) + (2 * c + 1) by omega] at hd
    rw [hmem_back hd]
    simpa [show guestBase + jtildeG + 3 + 2 * c = (guestBase + jtildeG + 2) + (2 * c + 1) by omega] using
      graphAt_edge_snd hcJ_at hc_lt_m
  have hm_kept_c : stK.mem ((guestBase + keptG + 1) + c) = kept_c := by
    have hd := hDisjKept (1 + c) (by omega)
    rw [hmem_back (by simpa [Nat.add_assoc] using hd)]
    simpa [kept_c, Nat.add_assoc, Nat.add_comm 1 c] using hkept_at (1 + c) (by simp; omega)
  have hm_eStep : stK.mem (jEsPtr + kept_c) = eStep := by
    rw [hmem_back (hDisjJE kept_c hkc_lt_jEs)]
    exact hjE_at kept_c hkc_lt_jEs
  have hk_ltw : k < 2 ^ w := by omega
  have h1k_ltw : 1 + k < 2 ^ w := by omega
  have h2k_ltw : 2 + k < 2 ^ w := by omega
  have h2v_ltw : 2 + P.verts.length < 2 ^ w := by omega
  have h2vk_ltw : 2 + P.verts.length + k < 2 ^ w := by omega
  have hwa1k_ltw : wAddr + (1 + k) < 2 ^ w := by omega
  have hwa2k_ltw : wAddr + (2 + k) < 2 ^ w := by omega
  have hwa2vk_ltw : wAddr + (2 + P.verts.length + k) < 2 ^ w := by omega
  have hjt_2c_ltw : (guestBase + jtildeG + 2) + 2 * c < 2 ^ w := by omega
  have hjt_2c1_ltw : (guestBase + jtildeG + 2) + (2 * c + 1) < 2 ^ w := by omega
  have hk_c_ltw : (guestBase + keptG + 1) + c < 2 ^ w := by omega
  have hjE_kc_ltw : jEsPtr + kept_c < 2 ^ w := by omega
  have h2c1_ltw : 2 * c + 1 < 2 ^ w := by omega
  have h2k'_ltw : 2 * k < 2 ^ w := by omega
  have h12k_ltw : 1 + 2 * k < 2 ^ w := by omega
  have hw0_2_2k_ltw : w0 + 1 + 2 * k + 1 < 2 ^ w := by omega
  let dirVal : ℕ := (if eG.1 = u then 1 else 0) * (if eG.2 = v then 1 else 0)
  have hdir_ltw : dirVal < 2 ^ w := by dsimp only [dirVal]; split_ifs <;> omega
  refine runs_start_le ?_
  dsimp only [gtDecodeInnerBody]
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := wAddr + (1 + k)) (v := u)
    (Expr.eval_add (Expr.eval_reg_of_eq hr_u)
      (Expr.eval_add (Expr.eval_const h1_lt) (Expr.eval_reg_of_eq hr17) h1k_ltw) hwa1k_ltw)
    hm_u) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := wAddr + (2 + k)) (v := v)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr_u]))
      (Expr.eval_add (Expr.eval_const h2_lt)
        (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr17])) h2k_ltw)
      hwa2k_ltw)
    hm_v) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := wAddr + (2 + P.verts.length + k)) (v := c)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr_u]))
      (Expr.eval_add
        (Expr.eval_add (Expr.eval_const h2_lt)
          (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr_14])) h2v_ltw)
        (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr17])) h2vk_ltw)
      hwa2vk_ltw)
    hm_c) ?_
  refine runs_seq_assign_le (v := 2 * c)
    (Expr.eval_mul (Expr.eval_const h2_lt) (Expr.eval_reg_of_eq (by simp [Function.update_self])) h2c_ltw) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := (guestBase + jtildeG + 2) + 2 * c) (v := eG.1)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr_8]))
      (Expr.eval_reg_of_eq (by simp [Function.update_self])) hjt_2c_ltw)
    hm_eG1) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := (guestBase + jtildeG + 2) + (2 * c + 1)) (v := eG.2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, hr_8]))
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne]))
        (Expr.eval_const h1_lt) h2c1_ltw)
      hjt_2c1_ltw)
    hm_eG2) ?_
  refine runs_seq_assign_le (v := dirVal)
    (Expr.eval_mul
      (Expr.eval_eq_op
        (Expr.eval_reg_of_eq (v := eG.1) (by simp [Function.update_of_ne]))
        (Expr.eval_reg_of_eq (v := u) (by simp [Function.update_of_ne])) h1_lt)
      (Expr.eval_eq_op
        (Expr.eval_reg_of_eq (v := eG.2) (by simp [Function.update_self]))
        (Expr.eval_reg_of_eq (v := v) (by simp [Function.update_of_ne])) h1_lt)
      hdir_ltw) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := (guestBase + keptG + 1) + c) (v := kept_c)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := guestBase + keptG + 1) (by simp [Function.update_of_ne, hr_9]))
      (Expr.eval_reg_of_eq (v := c) (by simp [Function.update_of_ne])) hk_c_ltw)
    hm_kept_c) ?_
  refine runs_seq_assign_le (Expr.eval_load_of_eq (x := jEsPtr + kept_c) (v := eStep)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := jEsPtr) (by simp [Function.update_of_ne, hr_1]))
      (Expr.eval_reg_of_eq (v := kept_c) (by simp [Function.update_self])) hjE_kc_ltw)
    hm_eStep) ?_
  refine runs_seq_assign_le (v := w0 + 1 + 2 * k)
    (Expr.eval_eq_of_eq
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := w0) (by simp [Function.update_of_ne, hr_7]))
        (Expr.eval_add (Expr.eval_const h1_lt)
          (Expr.eval_mul (Expr.eval_const h2_lt)
            (Expr.eval_reg_of_eq (v := k) (by simp [Function.update_of_ne, hr17])) h2k'_ltw)
          h12k_ltw)
        (by omega))
      (by omega)) ?_
  refine runs_seq_store_le (x := w0 + 1 + 2 * k) (v := eStep)
    (Expr.eval_reg_of_eq (v := w0 + 1 + 2 * k) (by simp [Function.update_self]))
    (Expr.eval_reg_of_eq (v := eStep) (by simp [Function.update_of_ne])) ?_
  refine runs_store_le (x := w0 + 1 + 2 * k + 1) (v := dirVal)
    (Expr.eval_add
      (Expr.eval_reg_of_eq (v := w0 + 1 + 2 * k) (by simp [Function.update_self]))
      (Expr.eval_const h1_lt) hw0_2_2k_ltw)
    (Expr.eval_reg_of_eq (v := dirVal) (by simp [Function.update_of_ne])) ?_ ?_
  · refine ⟨⟨fun r hr => ?_, by simp [Function.update_self], ?_, ?_, ?_⟩,
      by simp [Function.update_of_ne, hr17]⟩
    · dsimp only
      rw [Function.update_of_ne (by omega : r ≠ 17)]
      simp only [Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 26),
        Function.update_of_ne (by omega : r ≠ 25), Function.update_of_ne (by omega : r ≠ 24),
        Function.update_of_ne (by omega : r ≠ 23), Function.update_of_ne (by omega : r ≠ 22),
        Function.update_of_ne (by omega : r ≠ 21), Function.update_of_ne (by omega : r ≠ 20),
        Function.update_of_ne (by omega : r ≠ 19), Function.update_of_ne (by omega : r ≠ 18)]
      exact hregsK r hr
    · dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hmK_w0
    · intro t ht
      by_cases htk : t = k
      · subst htk
        refine ⟨hk_lt, ?_, ?_⟩
        · dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
          have hget := citedWalkSteps_getElem jEs cJtilde kept P.verts P.edges t hk_le
          rw [hget, List.getD_eq_getElem kept 0 hc_lt_kept]
          simpa [c, kept_c, eStep] using (List.getD_eq_getElem _ 0 hkc_lt_jEs).symm
        · dsimp only
          rw [Function.update_self]
          have hget := citedWalkSteps_getElem jEs cJtilde kept P.verts P.edges t hk_le
          rw [hget]
          have hdec : (if (cJtilde.edges.getD c (0, 0)).1 = u ∧ (cJtilde.edges.getD c (0, 0)).2 = v
              then 1 else 0) = dirVal := by
            have hcG : cJtilde.edges.getD c (0, 0) = eG := List.getD_eq_getElem _ _ hc_lt_m
            rw [hcG]; dsimp only [dirVal]
            by_cases h1 : eG.1 = u <;> by_cases h2 : eG.2 = v <;> simp [h1, h2]
          simpa [c, u, v] using hdec.symm
      · have hlt : t < k := by omega
        rcases hcellsK t hlt with ⟨htp, h1, h2⟩
        refine ⟨htp, ?_, ?_⟩
        · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h1
        · dsimp only; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact h2
    · intro addr haddr
      dsimp only
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hfrK addr (by rcases haddr with h | h; exact Or.inl h; exact Or.inr (by omega))
  · dsimp only [gtDecodeInnerBody, Expr.size]; omega

private lemma gtDecodeInnerLoop_triple {w : ℕ} {p : Program}
    {jEs kept : List ℕ} {cJtilde : Cited.Graph} {P : Walk}
    {mem mem2 : ℕ → ℕ} {stSteps : State} {dis : ℕ → Prop}
    {jEsPtr guestBase jtildeG keptG w0 wAddr : ℕ}
    (hw16 : 16 ≤ 2 ^ w)
    (heCap : ∀ idx ∈ jEs, idx < 2 ^ w)
    (hkept_lt : ∀ x ∈ kept, x < jEs.length)
    (hP_info : P.verts.length < 2 ^ w ∧ P.edges.length < 2 ^ w ∧
      wAddr + P.encode.length < 2 ^ w ∧
      (∀ c ∈ P.edges, c < cJtilde.m ∧ c < kept.length) ∧
      ∀ u ∈ P.verts, u < 2 ^ w)
    (hcJB : guestBase + jtildeG + cJtilde.encode.length < 2 ^ w)
    (hkeptB : guestBase + keptG + 1 + kept.length < 2 ^ w)
    (hjEB : jEsPtr + jEs.length < 2 ^ w)
    (hw_bound : w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) < 2 ^ w)
    (hcJ_w : ∀ i < cJtilde.m, (cJtilde.edges[i]!).1 < 2 ^ w ∧ (cJtilde.edges[i]!).2 < 2 ^ w)
    (hjE_at : ListAt mem jEsPtr jEs)
    (hcJ_at : GraphAt mem (guestBase + jtildeG) cJtilde)
    (hkept_at : ListAt mem (guestBase + keptG) (kept.length :: kept))
    (hwAddr_at : WalkAt mem wAddr P)
    (hAgree : ∀ {addr}, dis addr → mem2 addr = mem addr)
    (hDisjOut : ∀ {addr}, dis addr →
      addr < w0 ∨ w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) ≤ addr)
    (hDisjJE : ∀ i < jEs.length, dis (jEsPtr + i))
    (hDisjCJ : ∀ i < cJtilde.encode.length, dis (guestBase + jtildeG + i))
    (hDisjKept : ∀ i < 1 + kept.length, dis (guestBase + keptG + i))
    (hDisjWalk : ∀ i < P.encode.length, dis (wAddr + i))
    (hr_u : stSteps.regs 13 = wAddr)
    (hr_14 : stSteps.regs 14 = P.verts.length)
    (hr_8 : stSteps.regs 8 = guestBase + jtildeG + 2)
    (hr_9 : stSteps.regs 9 = guestBase + keptG + 1)
    (hr_1 : stSteps.regs 1 = jEsPtr)
    (hr_7 : stSteps.regs 7 = w0)
    (hr16 : stSteps.regs 16 = (citedWalkSteps jEs cJtilde kept P.verts P.edges).length)
    (hm2_w0 : mem2 w0 = (citedWalkSteps jEs cJtilde kept P.verts P.edges).length) :
    Triple w p
      (fun s' => (∀ r ≤ 16, s'.regs r = stSteps.regs r) ∧ s'.mem = mem2)
      (forRange 17 (.const 0) (.reg 16) gtDecodeInnerBody)
      (normalPost (gtDecodeInnerInv w0 (citedWalkSteps jEs cJtilde kept P.verts P.edges) mem2 stSteps
        (citedWalkSteps jEs cJtilde kept P.verts P.edges).length))
      (fun _ => (citedWalkSteps jEs cJtilde kept P.verts P.edges).length * (150 + Expr.size (.reg 16) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 16) + 5)) := by
  let dWalk := citedWalkSteps jEs cJtilde kept P.verts P.edges
  have hdWalk_len : dWalk.length = min (P.verts.length - 1) P.edges.length :=
    citedWalkSteps_length jEs cJtilde kept P.verts P.edges
  have hdWalk_ltw : dWalk.length < 2 ^ w := by rw [hdWalk_len]; omega
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  refine Triple.forRange_const 150 0 dWalk.length (Nat.zero_le _) h1_lt (fun _ => hdWalk_ltw)
    (fun s' ⟨hregs', hmem'⟩ => ⟨by simp [Expr.eval, h0_lt], by
      refine ⟨fun r hr => ?_, by simp, ?_, fun _ ht => (Nat.not_lt_zero _ ht).elim,
        fun addr _ => by rw [hmem']⟩
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hregs' r hr
      · rw [hmem']; exact hm2_w0⟩)
    (fun _ s' _ _ hI => hI.2.1)
    (fun _ s' _ _ hI => by simp [Expr.eval, hI.1 16 (by decide), hr16, dWalk]) ?_
  intro k _ hk_lt
  exact gtDecodeInnerBody_triple hw16 heCap hkept_lt hP_info hcJB hkeptB hjEB hw_bound
    hcJ_w hjE_at hcJ_at hkept_at hwAddr_at hAgree hDisjOut hDisjJE hDisjCJ hDisjKept hDisjWalk
    hr_u hr_14 hr_8 hr_9 hr_1 hr_7 hk_lt

theorem gtDecodeWalks_meetsContract {w eCap : ℕ} {p : Program} {bRev : ℕ}
    {J : MGraph} {jEs kept : List ℕ} {cJtilde : Cited.Graph} {embJJtilde : ℕ → Walk}
    (hpRev : p.HasAt bRev gtRevPrimProcs) :
    MeetsContract w p (bRev + gtIdxDecodeWalks)
      (gtDecodeWalksContract w eCap J jEs kept cJtilde embJJtilde) := by
  refine meetsContract_of_runs
    (hpRev.get (i := gtIdxDecodeWalks) (by simp [gtRevPrimProcs, gtIdxDecodeWalks]))
    fun args mem pos ω hargs hpre => ?_
  rcases hpre with ⟨mJ, jEsPtr, guestBase, jtildeG, keptG, embG, mEmbOutPtr, walkBufPtr,
    rfl, hmJ_eq, hw16, hjEB, hcJB, hkeptB, hembB, hmEB, hwkB, hjE_eq, heCap,
    hkept_lt, hembWalks, hcJall, hcJ_w, hjE_at, hcJ_at, hkept_at, hemb_at,
    hmEW_disj, hdisjJE, hdisjCJ, hdisjKept, hdisjEmb, hdisjWalk⟩
  let decWalk : ℕ → List (ℕ × Bool) := citedDecWalk jEs cJtilde kept embJJtilde
  let prefLen : ℕ → ℕ := citedDecPrefLen jEs cJtilde kept embJJtilde
  let totWalk := prefLen jEs.length
  let dis : ℕ → Prop := fun addr =>
    (addr < mEmbOutPtr ∨ mEmbOutPtr + eCap ≤ addr) ∧ (addr < walkBufPtr ∨ walkBufPtr + totWalk ≤ addr)
  have hlt_mJ : jEs.length < 2 ^ w := hargs jEs.length (by simp)
  have hlt_jEP : jEsPtr < 2 ^ w := hargs jEsPtr (by simp)
  have hlt_gB : guestBase < 2 ^ w := hargs guestBase (by simp)
  have hlt_jtG : jtildeG < 2 ^ w := hargs jtildeG (by simp)
  have hlt_kG : keptG < 2 ^ w := hargs keptG (by simp)
  have hlt_eG : embG < 2 ^ w := hargs embG (by simp)
  have hlt_mEP : mEmbOutPtr < 2 ^ w := hargs mEmbOutPtr (by simp)
  have hlt_wBP : walkBufPtr < 2 ^ w := hargs walkBufPtr (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  have hjt2_ltw : guestBase + jtildeG + 2 < 2 ^ w := by
    have hcl : 2 ≤ cJtilde.encode.length := by rw [graph_encode_length]; omega
    omega
  have hjtilde2_ltw : jtildeG + 2 < 2 ^ w := by omega
  have hkept1_ltw : keptG + 1 < 2 ^ w := by omega
  have hk1_ltw : guestBase + keptG + 1 < 2 ^ w := by omega
  have heG_ltw : guestBase + embG < 2 ^ w := by omega
  have hjE_nd : jEs.Nodup := hjE_eq ▸ vertsOf_nodup J.E
  have heCap_word : ∀ idx ∈ jEs, idx < 2 ^ w := fun idx hi => by
    have hmem : idx ∈ vertsOf J.E := hjE_eq ▸ hi
    rw [mem_vertsOf] at hmem
    have := heCap idx hmem
    omega
  have hdisj_mw : ∀ {addr : ℕ}, dis addr →
      ∀ j, j ≤ jEs.length →
      (addr < mEmbOutPtr ∨ mEmbOutPtr + eCap ≤ addr) ∧ (addr < walkBufPtr ∨ walkBufPtr + prefLen j ≤ addr) := by
    intro addr ⟨h1, h2⟩ j hj
    refine ⟨h1, h2.imp_right fun h => ?_⟩
    exact le_trans (Nat.add_le_add_left (citedDecPrefLen_mono jEs cJtilde kept embJJtilde hj) _) h
  refine runs_start_le ?_
  dsimp only [gtRevPrimProcs, gtIdxDecodeWalks, List.getElem_cons_succ, List.getElem_cons_zero,
    gtDecodeWalksStmt]
  refine runs_seq_assign_le (v := guestBase + jtildeG + 2)
    (by simp [Expr.eval, BinOp.eval, startState, h2_lt, hjtilde2_ltw,
      show guestBase + (jtildeG + 2) = guestBase + jtildeG + 2 by omega, hjt2_ltw]) ?_
  refine runs_seq_assign_le (v := guestBase + keptG + 1)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, startState, h1_lt, hkept1_ltw,
      show guestBase + (keptG + 1) = guestBase + keptG + 1 by omega, hk1_ltw]) ?_
  refine runs_seq_assign_le (v := guestBase + embG)
    (by simp [Expr.eval, BinOp.eval, Function.update_of_ne, startState, heG_ltw]) ?_
  let outerBody : Stmt :=
    .assign 12 (.load (.bin .add (.reg 1) (.reg 11))) ;;
    .store (.bin .add (.reg 6) (.reg 12)) (.reg 7) ;;
    .assign 13 (.bin .add (.reg 2) (.load (.bin .add (.reg 10) (.reg 11)))) ;;
    .assign 14 (.load (.reg 13)) ;;
    .assign 15 (.load (.bin .add (.reg 13) (.bin .add (.const 1) (.reg 14)))) ;;
    gtComputeStepsStmt ;;
    .store (.reg 7) (.reg 16) ;;
    forRange 17 (.const 0) (.reg 16) gtDecodeInnerBody ;;
    .assign 7 (.bin .add (.reg 7) (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 16))))
  let InvOut : ℕ → State → Prop := fun k s =>
    s.regs 0 = jEs.length ∧ s.regs 1 = jEsPtr ∧ s.regs 2 = guestBase ∧
    s.regs 3 = jtildeG ∧ s.regs 4 = keptG ∧ s.regs 5 = embG ∧
    s.regs 6 = mEmbOutPtr ∧ s.regs 7 = walkBufPtr + prefLen k ∧
    s.regs 8 = guestBase + jtildeG + 2 ∧ s.regs 9 = guestBase + keptG + 1 ∧
    s.regs 10 = guestBase + embG ∧ s.regs 11 = k ∧
    (∀ i (hi : i < k), ∃ hiJ : i < jEs.length,
      s.mem (mEmbOutPtr + jEs[i]'hiJ) = walkBufPtr + prefLen i ∧
      MWalkAt s.mem (walkBufPtr + prefLen i) (decWalk i)) ∧
    ∀ addr,
      (addr < mEmbOutPtr ∨ mEmbOutPtr + eCap ≤ addr) →
      (addr < walkBufPtr ∨ walkBufPtr + prefLen k ≤ addr) →
      s.mem addr = mem addr
  let stepCost : ℕ → ℕ := fun k => 250 * (embJJtilde k).edges.length + 185
  have hloop : Triple w p
      (fun s =>
        s.regs 0 = jEs.length ∧ s.regs 1 = jEsPtr ∧ s.regs 2 = guestBase ∧
        s.regs 3 = jtildeG ∧ s.regs 4 = keptG ∧ s.regs 5 = embG ∧
        s.regs 6 = mEmbOutPtr ∧ s.regs 7 = walkBufPtr ∧
        s.regs 8 = guestBase + jtildeG + 2 ∧ s.regs 9 = guestBase + keptG + 1 ∧
        s.regs 10 = guestBase + embG ∧
        ∀ addr, s.mem addr = mem addr)
      (forRange 11 (.const 0) (.reg 0) outerBody)
      (normalPost (InvOut jEs.length))
      (fun _ => rangeCost stepCost 0 jEs.length +
        jEs.length * (Expr.size (.reg 0) + 8) +
        (Expr.size (.const 0) + Expr.size (.reg 0) + 5)) := by
    refine Triple.forRange_le stepCost 0 jEs.length (Nat.zero_le _) h1_lt (fun _ => hlt_mJ)
      (fun s hI => ⟨by simp [Expr.eval, h0_lt], by
        rcases hI with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, hmem⟩
        exact ⟨by simpa [Function.update_of_ne] using r0, by simpa [Function.update_of_ne] using r1,
          by simpa [Function.update_of_ne] using r2, by simpa [Function.update_of_ne] using r3,
          by simpa [Function.update_of_ne] using r4, by simpa [Function.update_of_ne] using r5,
          by simpa [Function.update_of_ne] using r6,
          by simpa [Function.update_of_ne, prefLen, citedDecPrefLen] using r7,
          by simpa [Function.update_of_ne] using r8, by simpa [Function.update_of_ne] using r9,
          by simpa [Function.update_of_ne] using r10, by simp,
          fun _ hi => (Nat.not_lt_zero _ hi).elim, fun addr _ _ => hmem addr⟩⟩)
      (fun _ s _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.1)
      (fun _ s _ _ hI => by simp [Expr.eval, hI.1]) ?_
    intro j _ hj_lt s ω' ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, hdone, hfr⟩
    set eOrig := jEs[j]'hj_lt
    have heJ : eOrig ∈ J.E := by
      have hm : eOrig ∈ vertsOf J.E := hjE_eq ▸ List.getElem_mem hj_lt
      rwa [mem_vertsOf] at hm
    have heCap_j : eOrig < eCap := heCap eOrig heJ
    have hP_info := hembWalks j hj_lt
    set wOff := mem (guestBase + embG + j)
    set wAddr := guestBase + wOff
    set P := embJJtilde j
    set dWalk := decWalk j
    have hdWalk_len : dWalk.length = min (P.verts.length - 1) P.edges.length :=
      citedWalkSteps_length jEs cJtilde kept P.verts P.edges
    have hdWalk_le : dWalk.length ≤ P.edges.length := by
      rw [hdWalk_len]; exact Nat.min_le_right _ _
    have hj_le : j ≤ jEs.length := Nat.le_of_lt hj_lt
    have hj1_le : j + 1 ≤ jEs.length := hj_lt
    have hpref_j_le : prefLen j ≤ totWalk := citedDecPrefLen_mono jEs cJtilde kept embJJtilde hj_le
    have hpref_j1_le : prefLen (j + 1) ≤ totWalk := citedDecPrefLen_mono jEs cJtilde kept embJJtilde hj1_le
    have hw0_def : prefLen (j + 1) = prefLen j + (1 + 2 * dWalk.length) := by
      simp only [prefLen, citedDecPrefLen, mWalkEncode_length]; rfl
    set w0 := walkBufPtr + prefLen j
    have hw0_ltw : w0 < 2 ^ w := by dsimp only [w0, totWalk, prefLen] at *; omega
    have hw1_ltw : w0 + (1 + 2 * dWalk.length) < 2 ^ w := by
      dsimp only [w0, totWalk, prefLen] at *; rw [Nat.add_assoc, ← hw0_def]; omega
    have hw_bound : w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) < 2 ^ w := by
      rw [← hdWalk_len]; omega
    have hw0_end : w0 + 1 + 2 * dWalk.length = walkBufPtr + prefLen (j + 1) := by
      dsimp only [w0]; rw [hw0_def]; omega
    have hw1_tot : w0 + 1 + 2 * dWalk.length ≤ walkBufPtr + citedDecPrefLen jEs cJtilde kept embJJtilde jEs.length := by
      rw [hw0_end]; exact Nat.add_le_add_left hpref_j1_le _
    have hw0_ge : walkBufPtr ≤ w0 := by dsimp only [w0]; exact Nat.le_add_right _ _
    have hEW : mEmbOutPtr + eCap ≤ w0 ∨ w0 + 1 + 2 * dWalk.length ≤ mEmbOutPtr := by
      rcases hmEW_disj with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have h_mE_ltw : mEmbOutPtr + eOrig < 2 ^ w := by omega
    have hwAddr_at : WalkAt mem wAddr P := by
      simpa [wAddr, wOff, Nat.add_assoc] using hemb_at j hj_lt
    have hwAddr_ltw : wAddr + (Walk.encode P).length < 2 ^ w := by
      simpa [wAddr, wOff, Nat.add_assoc] using hP_info.2.2.1
    have hwOff_ltw : wOff < 2 ^ w := by omega
    have hw_vLen_ltw : P.verts.length < 2 ^ w := hP_info.1
    have hw_eLen_ltw : P.edges.length < 2 ^ w := hP_info.2.1
    have hw_1v_ltw : 1 + P.verts.length < 2 ^ w := by rw [walk_encode_length] at hwAddr_ltw; omega
    have hw_1v_addr_ltw : wAddr + (1 + P.verts.length) < 2 ^ w := by
      rw [walk_encode_length] at hwAddr_ltw; omega
    have h_embPtr_ltw : guestBase + embG + j < 2 ^ w := by omega
    have hj_ltw : j < 2 ^ w := by omega
    have hm_eOrig : s.mem (jEsPtr + j) = eOrig := by
      have hd := hdisj_mw (hdisjJE j hj_lt) j hj_le
      rw [hfr _ hd.1 hd.2]; exact hjE_at j hj_lt
    have hm_wOff : s.mem (guestBase + embG + j) = wOff := by
      have hd := hdisj_mw (hdisjEmb j hj_lt) j hj_le
      rw [hfr _ hd.1 hd.2]
    have hm_vLen : s.mem wAddr = P.verts.length := by
      have h0 := hdisj_mw (hdisjWalk j hj_lt 0 (by rw [walk_encode_length]; omega)) j hj_le
      simp only [Nat.add_zero] at h0
      rw [hfr _ h0.1 h0.2]; exact hwAddr_at.verts_len
    have hm_eLen : s.mem (wAddr + (1 + P.verts.length)) = P.edges.length := by
      have hi : 1 + P.verts.length < (Walk.encode P).length := by rw [walk_encode_length]; omega
      have h0 := hdisj_mw (hdisjWalk j hj_lt _ hi) j hj_le
      rw [hfr _ h0.1 h0.2]
      simpa [wAddr, wOff, Nat.add_assoc] using hwAddr_at.edges_len
    refine runs_start_le ?_
    dsimp only [outerBody]
    refine runs_seq_assign_le (Expr.eval_load_of_eq (v := eOrig)
      (by simp [Expr.eval, BinOp.eval, r1, r11, (by omega : jEsPtr + j < 2 ^ w)]) hm_eOrig) ?_
    refine runs_seq_store_le (x := mEmbOutPtr + eOrig) (v := w0)
      (by simp [Expr.eval, BinOp.eval, Function.update_self, r6, h_mE_ltw])
      (by simp [Expr.eval, Function.update_of_ne, r7]) ?_
    let mem1 := Function.update s.mem (mEmbOutPtr + eOrig) w0
    have hfr1 : ∀ addr, addr ≠ mEmbOutPtr + eOrig → mem1 addr = s.mem addr := fun addr hne =>
      Function.update_of_ne hne _ _
    have hwOff_ne : guestBase + embG + j ≠ mEmbOutPtr + eOrig := by
      rcases (hdisjEmb j hj_lt).1 with h | h <;> omega
    have hwAddr_ne : ∀ i < (Walk.encode P).length, wAddr + i ≠ mEmbOutPtr + eOrig := fun i hi => by
      rcases (hdisjWalk j hj_lt i (by simpa [wAddr, wOff, Nat.add_assoc] using hi)).1 with h | h <;> omega
    have hm_wOff1 : Function.update s.mem (mEmbOutPtr + eOrig) w0 (guestBase + embG + j) = wOff := by
      rw [Function.update_of_ne hwOff_ne, hm_wOff]
    refine runs_seq_assign_le (v := wAddr)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, r2]))
        (Expr.eval_load_of_eq (x := guestBase + embG + j)
          (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, r10]))
            (Expr.eval_reg_of_eq (by simp [Function.update_of_ne, r11]))
            h_embPtr_ltw)
          hm_wOff1)
        (by omega)) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (x := wAddr) (v := P.verts.length)
      (Expr.eval_reg_of_eq (v := wAddr) (by simp [Function.update_self]))
      (by dsimp only
          rw [Function.update_of_ne (by simpa [Nat.add_zero] using hwAddr_ne 0 (by rw [walk_encode_length]; omega)),
            hm_vLen])) ?_
    refine runs_seq_assign_le (Expr.eval_load_of_eq (x := wAddr + (1 + P.verts.length)) (v := P.edges.length)
      (Expr.eval_add
        (Expr.eval_reg_of_eq (v := wAddr) (by simp [Function.update_of_ne, Function.update_self]))
        (Expr.eval_add (Expr.eval_const h1_lt)
          (Expr.eval_reg_of_eq (v := P.verts.length) (by simp [Function.update_self])) hw_1v_ltw)
        hw_1v_addr_ltw)
      (by dsimp only
          rw [Function.update_of_ne (hwAddr_ne _ (by rw [walk_encode_length]; omega)), hm_eLen])) ?_
    refine runs_seq_gtComputeSteps_le (eLen := P.edges.length) hw16
      (by simp [Function.update_of_ne, Function.update_self])
      (by simp [Function.update_self]) hw_vLen_ltw
      fun stSteps hr16 hsmem _ hregs_eq => ?_
    rw [← hdWalk_len] at hr16
    refine runs_seq_store_le (x := w0) (v := dWalk.length)
      (Expr.eval_reg_of_eq (v := w0) (by rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, r7]))
      (Expr.eval_reg_of_eq (v := dWalk.length) hr16) ?_
    let mem2 := Function.update mem1 w0 dWalk.length
    have hfr2 : ∀ addr, addr < w0 ∨ w0 + 1 ≤ addr → mem2 addr = mem1 addr := fun addr hne =>
      Function.update_of_ne (by omega) _ _
    have hAgree : ∀ {addr}, dis addr → mem2 addr = mem addr := by
      intro addr ⟨hdm, hdw⟩
      have hne_w0 : addr ≠ w0 := by rcases hdw with h | h <;> omega
      have hne_mE : addr ≠ mEmbOutPtr + eOrig := by rcases hdm with h | h <;> omega
      have hdw_j : addr < walkBufPtr ∨ walkBufPtr + prefLen j ≤ addr :=
        hdw.imp_right fun h => le_trans (Nat.add_le_add_left hpref_j_le _) h
      rw [hfr2 addr (by rcases hne_w0.lt_or_gt with h | h <;> omega), hfr1 addr hne_mE, hfr addr hdm hdw_j]
    have hDisjOut : ∀ {addr}, dis addr →
        addr < w0 ∨ w0 + 1 + 2 * (min (P.verts.length - 1) P.edges.length) ≤ addr := by
      intro addr ⟨_, hdw⟩
      rw [← hdWalk_len]
      rcases hdw with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
    have hr_u_s : stSteps.regs 13 = wAddr := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, Function.update_self]
    have hr_14_s : stSteps.regs 14 = P.verts.length := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, Function.update_self]
    have hr_8_s : stSteps.regs 8 = guestBase + jtildeG + 2 := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, r8]
    have hr_9_s : stSteps.regs 9 = guestBase + keptG + 1 := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, r9]
    have hr_1_s : stSteps.regs 1 = jEsPtr := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, r1]
    have hr_7_s : stSteps.regs 7 = w0 := by
      rw [hregs_eq _ (by decide)]; simp [Function.update_of_ne, r7]
    have hm2_w0 : mem2 w0 = dWalk.length := by dsimp only [mem2]; simp [Function.update_self]
    have hDisjW_j : ∀ i < P.encode.length, dis (wAddr + i) := fun i hi => by
      simpa [wAddr, wOff, Nat.add_assoc] using hdisjWalk j hj_lt i hi
    have hInnerLoop := gtDecodeInnerLoop_triple (p := p) (mem := mem) (mem2 := mem2) (stSteps := stSteps)
      hw16 heCap_word hkept_lt ⟨hw_vLen_ltw, hw_eLen_ltw, hwAddr_ltw, hP_info.2.2.2.1, hP_info.2.2.2.2⟩
      hcJB hkeptB hjEB hw_bound hcJ_w hjE_at hcJ_at hkept_at hwAddr_at
      hAgree hDisjOut hdisjJE hdisjCJ hdisjKept hDisjW_j
      hr_u_s hr_14_s hr_8_s hr_9_s hr_1_s hr_7_s hr16 hm2_w0
    refine runs_seq_triple_le hInnerLoop
      ⟨fun _ _ => rfl, by simp [mem2, mem1, hsmem]⟩ ?_
    intro stIn ⟨hregsIn, _, hmIn_w0, hcellsIn, hfrIn⟩
    have hw_12d_ltw : 1 + 2 * dWalk.length < 2 ^ w := by omega
    have hr7_in : stIn.regs 7 = w0 := by rw [hregsIn 7 (by decide), hr_7_s]
    have hr16_in : stIn.regs 16 = dWalk.length := by rw [hregsIn 16 (by decide), hr16]
    have hmw_done : MWalkAt stIn.mem w0 dWalk := mWalkAt_of_cells hmIn_w0 fun i hi => by
      rcases hcellsIn i hi with ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    refine runs_assign_le (v := walkBufPtr + prefLen (j + 1))
      (Expr.eval_eq_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq (v := w0) hr7_in)
          (Expr.eval_add (Expr.eval_const h1_lt)
            (Expr.eval_mul (Expr.eval_const h2_lt)
              (Expr.eval_reg_of_eq (v := dWalk.length) hr16_in) (by omega))
            hw_12d_ltw)
          (by dsimp only [w0]; omega))
        (by dsimp only [w0]; rw [Nat.add_assoc, ← hw0_def]))
      ⟨⟨by simp [Function.update_of_ne, hregsIn 0 (by decide), hregs_eq 0 (by decide), r0],
        by simp [Function.update_of_ne, hregsIn 1 (by decide), hregs_eq 1 (by decide), r1],
        by simp [Function.update_of_ne, hregsIn 2 (by decide), hregs_eq 2 (by decide), r2],
        by simp [Function.update_of_ne, hregsIn 3 (by decide), hregs_eq 3 (by decide), r3],
        by simp [Function.update_of_ne, hregsIn 4 (by decide), hregs_eq 4 (by decide), r4],
        by simp [Function.update_of_ne, hregsIn 5 (by decide), hregs_eq 5 (by decide), r5],
        by simp [Function.update_of_ne, hregsIn 6 (by decide), hregs_eq 6 (by decide), r6],
        by simp [Function.update_of_ne, Function.update_self],
        by simp [Function.update_of_ne, hregsIn 8 (by decide), hr_8_s],
        by simp [Function.update_of_ne, hregsIn 9 (by decide), hr_9_s],
        by simp [Function.update_of_ne, hregsIn 10 (by decide), hregs_eq 10 (by decide), r10],
        by simp [Function.update_self],
        ?_, ?_⟩,
       by simp [Function.update_of_ne, hregsIn 11 (by decide), hregs_eq 11 (by decide), r11]⟩
      ?_
    · intro i hi
      by_cases hij : i = j
      · subst hij
        refine ⟨hj_lt, ?_, hmw_done⟩
        have hdis_i : mEmbOutPtr + eOrig < w0 + 1 ∨ w0 + 1 + 2 * dWalk.length ≤ mEmbOutPtr + eOrig := by
          rcases hEW with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
        rw [hfrIn _ hdis_i,
          hfr2 _ (by rcases hEW with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
        simp [mem1, w0]
      · have hilt : i < j := by omega
        rcases hdone i hilt with ⟨hiJ, hp_i, hmw_i⟩
        have hpre_i1_le : prefLen (i + 1) ≤ prefLen j :=
          citedDecPrefLen_mono jEs cJtilde kept embJJtilde hilt
        have h_i_end : walkBufPtr + prefLen i + (1 + 2 * (decWalk i).length) ≤ w0 := by
          have : prefLen (i + 1) = prefLen i + (1 + 2 * (decWalk i).length) := by
            simp [prefLen, citedDecPrefLen, mWalkEncode_length, decWalk]
          omega
        refine ⟨hiJ, ?_, ?_⟩
        · have he_lt : jEs[i]'hiJ < eCap := by
            apply heCap
            have hm : jEs[i]'hiJ ∈ vertsOf J.E := hjE_eq ▸ List.getElem_mem hiJ
            rwa [mem_vertsOf] at hm
          have hdis_i : mEmbOutPtr + jEs[i]'hiJ < w0 + 1 ∨ w0 + 1 + 2 * dWalk.length ≤ mEmbOutPtr + jEs[i]'hiJ := by
            rcases hEW with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]
          have hne_i : mEmbOutPtr + jEs[i]'hiJ ≠ mEmbOutPtr + eOrig := by
            intro heq
            exact hij ((hjE_nd.getElem_inj_iff).mp (by omega))
          rw [hfrIn _ hdis_i,
            hfr2 _ (by rcases hEW with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)]),
            hfr1 _ hne_i]
          exact hp_i
        · refine hmw_i.of_agree fun addr h1 h2 => ?_
          rw [hfrIn addr (Or.inl (by omega)), hfr2 addr (Or.inl (by omega)),
            hfr1 addr (by rcases hEW with h | h <;> omega)]
    · intro addr hdm hdw
      have hdw_in : addr < w0 + 1 ∨ w0 + 1 + 2 * dWalk.length ≤ addr := by
        rcases hdw with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
      have hdw2 : addr < w0 ∨ w0 + 1 ≤ addr := by
        rcases hdw with h | h; exact Or.inl (by omega); exact Or.inr (by omega)
      have hdw0 : addr < walkBufPtr ∨ walkBufPtr + prefLen j ≤ addr := by
        rcases hdw with h | h; exact Or.inl h
        exact Or.inr (by omega)
      rw [hfrIn addr hdw_in, hfr2 addr hdw2, hfr1 addr (by rcases hdm with h | h <;> omega)]
      exact hfr addr hdm hdw0
    · have hP_ed : (citedWalkSteps jEs cJtilde kept P.verts P.edges).length ≤ (embJJtilde j).edges.length :=
        hdWalk_le
      dsimp only [outerBody, gtComputeStepsStmt, stepCost, Expr.size]
      omega
  refine runs_seq_triple_le hloop
    ⟨by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne, startState], by simp [Function.update_of_ne, startState],
     by simp [Function.update_of_ne], by simp [Function.update_of_ne], by simp [Function.update_self],
     fun _ => rfl⟩ ?_
  intro st' ⟨_, _, _, _, _, _, _, hr7', _, _, _, _, hdone', hfr'⟩
  refine runs_ret_le (v := walkBufPtr + totWalk)
    (by simp [Expr.eval, hr7', totWalk, prefLen])
    ⟨jEsPtr, guestBase, jtildeG, keptG, embG, mEmbOutPtr, walkBufPtr, rfl, rfl, ?_, ?_, hfr'⟩ ?_
  · intro e he
    refine ⟨heCap e he, ?_⟩
    have hm : e ∈ vertsOf J.E := mem_vertsOf.mpr he
    rw [← hjE_eq] at hm
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hm
    rcases hdone' j hj with ⟨_, hp, hmw⟩
    rw [hp, citedEmbToMGraph_at_jEs hjE_eq hj]
    exact hmw
  · intro j hj
    rcases hdone' j hj with ⟨_, hp, _⟩
    rw [hp]
    refine ⟨Nat.le_add_right _ _, ?_⟩
    have hsucc : prefLen (j + 1) = prefLen j + (mWalkEncode (decWalk j)).length := by
      simp only [prefLen, citedDecPrefLen]; rfl
    rw [Nat.add_assoc, ← hsucc]
    exact Nat.add_le_add_left (citedDecPrefLen_mono jEs cJtilde kept embJJtilde hj) _
  · have hrc : rangeCost stepCost 0 jEs.length =
        250 * ((List.range jEs.length).map fun j => (embJJtilde j).edges.length).sum +
        185 * jEs.length := by
      rw [rangeCost_zero_eq_range]
      induction jEs.length with
      | zero => simp
      | succ m ih =>
        rw [List.range_succ, List.map_append, List.sum_append,
          List.map_append, List.sum_append, ih]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, stepCost]
        ring
    dsimp only [gtDecodeWalksContract, Expr.size] at hrc ⊢
    simp only [List.getD_cons_zero]
    omega

end

end MinCostFlow.DynSpanner.Program
