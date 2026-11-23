module

public import MinCostFlow.Spanner.ProgTask3DrainProof

@[expose] public section

namespace MinCostFlow.Spanner

open WordRAM Cited

/-!
# Walk Vertex-Copy Loop and `t3EdgeStep` Invariants for `t3MiddleEdge`

Proves walk/econg helper lemmas, `t3CopyVert_ptriple`, and `T3EdgeStepInv`.
-/

lemma t3_isWalk_verts_len_le {G : Graph} {u v : ℕ} {P : Walk}
    (hW : P.IsWalk G u v) : P.verts.length ≤ P.edges.length + 1 := by
  rcases hW with ⟨_, _, ⟨hv, he, _⟩ | ⟨_, hvlen, _⟩⟩
  · simp [hv, he]
  · omega

lemma t3_isWalk_verts_lt {G : Graph} {u v : ℕ} {P : Walk}
    (hG : G.IsValid) (hW : P.IsWalk G u v) :
    ∀ x ∈ P.verts, x < G.n := by
  rcases hW with ⟨hu, hv, ⟨hve, _, _⟩ | ⟨_, hvlen, _, hlast, hedges_lt, hmatch⟩⟩
  · intro x hx; rw [hve] at hx; simp at hx
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rcases Nat.lt_trichotomy i P.edges.length with hi_e | rfl | hi_gt
    · have he_mem : P.edges.getD i 0 ∈ P.edges := by
        rw [List.getD_eq_getElem _ _ hi_e]; exact List.getElem_mem hi_e
      have he_lt : P.edges.getD i 0 < G.edges.length := hedges_lt _ he_mem
      have hmem_G : G.edges.getD (P.edges.getD i 0) (0, 0) ∈ G.edges := by
        rw [List.getD_eq_getElem _ _ he_lt]; exact List.getElem_mem he_lt
      have hedge := hG _ hmem_G
      have hm := hmatch i hi_e
      have hget0 : P.verts.getD i 0 = P.verts[i] := List.getD_eq_getElem _ _ hi
      rcases hm with ⟨hm1, _⟩ | ⟨hm1, _⟩
      · rw [← hget0, ← hm1]; exact hedge.1
      · rw [← hget0, ← hm1]; exact hedge.2
    · have hne : P.verts ≠ [] := fun h => by rw [h] at hvlen; simp at hvlen
      rw [List.getLast?_eq_some_getLast hne] at hlast
      have hlast_eq : P.verts[P.edges.length]'hi = v := by
        have := Option.some.inj hlast
        simpa [List.getLast_eq_getElem, hvlen] using this
      rw [hlast_eq]; exact hv
    · omega

lemma t3_econg_eq_take_step {J : Graph} {emb : ℕ → Option Walk} {eJ : ℕ}
    {P_lift : Walk} {k : ℕ} (heJ : eJ < J.m) (hunemb : emb eJ = none)
    (hnd : P_lift.edges.Nodup) (hk : k < P_lift.edges.length) :
    let embK : ℕ → ℕ → Option Walk := fun i =>
      Function.update emb eJ (some ⟨P_lift.verts, P_lift.edges.take i⟩)
    let eW := P_lift.edges[k]'hk
    {j ∈ Finset.range J.m | eW ∈ (partialToWalk (embK (k + 1)) j).edges}.card =
      {j ∈ Finset.range J.m | eW ∈ (partialToWalk (embK k) j).edges}.card + 1 ∧
    ∀ eW', eW' ≠ eW →
      {j ∈ Finset.range J.m | eW' ∈ (partialToWalk (embK (k + 1)) j).edges}.card =
        {j ∈ Finset.range J.m | eW' ∈ (partialToWalk (embK k) j).edges}.card := by
  intro embK eW
  have htake : P_lift.edges.take (k + 1) = P_lift.edges.take k ++ [eW] :=
    List.take_add_one.trans (by simp [List.getElem?_eq_getElem hk, eW])
  have hnot : eW ∉ P_lift.edges.take k := by
    intro hmem
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.mp hmem
    have hj_len : j < P_lift.edges.length := by rw [List.length_take] at hj; omega
    have hj_lt : j < k := by rw [List.length_take] at hj; omega
    rw [List.getElem_take] at hje
    have hinj := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨j, hj_len⟩) (a₂ := ⟨k, hk⟩) hje
    simp at hinj; omega
  have hS_eq : {j ∈ Finset.range J.m | eW ∈ (partialToWalk (embK (k + 1)) j).edges} =
      insert eJ {j ∈ Finset.range J.m | eW ∈ (partialToWalk (embK k) j).edges} := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    dsimp only [embK, partialToWalk]
    by_cases hj : j = eJ
    · subst hj
      simp only [Function.update_self, Option.getD_some, htake, List.mem_append, List.mem_singleton,
        or_true, hnot, heJ, true_and, or_false]
    · simp only [Function.update_of_ne hj]
      exact ⟨fun ⟨h1, h2⟩ => Or.inr ⟨h1, h2⟩, fun h => h.elim (fun heq => absurd heq hj) id⟩
  have heJ_not : eJ ∉ {j ∈ Finset.range J.m | eW ∈ (partialToWalk (embK k) j).edges} := by
    simp only [Finset.mem_filter, Finset.mem_range]
    dsimp only [embK, partialToWalk]
    simp [Function.update_self, hnot]
  refine ⟨?_, fun eW' hne => ?_⟩
  · rw [hS_eq, Finset.card_insert_of_notMem heJ_not]
  · congr 1; ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    dsimp only [embK, partialToWalk]
    by_cases hj : j = eJ
    · subst hj; simp only [Function.update_self, Option.getD_some, htake, List.mem_append,
        List.mem_singleton, hne, or_false]
    · simp only [Function.update_of_ne hj]

lemma t3_econg_eq_take_zero {J : Graph} {emb : ℕ → Option Walk} {eJ : ℕ}
    {verts : List ℕ} (hunemb : emb eJ = none) (eW : ℕ) :
    {j ∈ Finset.range J.m |
      eW ∈ (partialToWalk (Function.update emb eJ (some ⟨verts, []⟩)) j).edges}.card =
      {j ∈ Finset.range J.m | eW ∈ (partialToWalk emb j).edges}.card := by
  congr 1; ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  dsimp only [partialToWalk]
  by_cases hj : j = eJ
  · subst hj; simp only [Function.update_self, Option.getD_some, hunemb, Option.getD_none,
      Walk.empty, List.not_mem_nil]
  · simp only [Function.update_of_ne hj]

lemma t3_edgeStep_econg_le_round {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW rCur cntOld : ℕ}
    (hge : (inp.mkWitnessData ce pds WSubs).j0Edges.length ≤ eW)
    (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m)
    (hle_old : (cntOld : ℝ) / (inp.mkWitnessData ce pds WSubs).wW eW ≤
      (rCur : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₂) :
    ((cntOld + 1 : ℕ) : ℝ) / (inp.mkWitnessData ce pds WSubs).wW eW ≤
      ((rCur : ℝ) + 1 / 2) * (inp.mkWitnessData ce pds WSubs).τ₂ := by
  let wd := inp.mkWitnessData ce pds WSubs
  have hw_pos : 0 < wd.wW eW := mkW_wW_pos (hok (exists_localSpannerTools 0 0).some) hws heW
  have htwo := mkW_two_le_tau2_wW_comp hok hws hge heW
  have hinv : (1 : ℝ) / wd.wW eW ≤ wd.τ₂ / 2 := by
    rw [div_le_div_iff₀ hw_pos (by norm_num)]; linarith
  have hsplit : ((cntOld + 1 : ℕ) : ℝ) / wd.wW eW = (cntOld : ℝ) / wd.wW eW + 1 / wd.wW eW := by
    push_cast; ring
  rw [hsplit]; linarith

lemma t3_edgeStep_rCur_le_cnt {inp : WitnessCoreInput} {ce : ConstructExpanderImpl}
    {pds : PathDSParams} {WSubs : List Graph}
    (hok : ∀ {N_max : ℕ} {W_max : ℝ} (tools : LocalSpannerTools N_max W_max),
      WitnessOK (N_max := N_max) (W_max := W_max) tools inp.H' inp.prep.J inp.embJH
        (inp.mkWitnessData ce pds WSubs))
    (hws : inp.ValidWSubs ce WSubs)
    {eW rCur cntNew : ℕ}
    (hge : (inp.mkWitnessData ce pds WSubs).j0Edges.length ≤ eW)
    (heW : eW < (inp.mkWitnessData ce pds WSubs).W.m)
    (hle : (rCur : ℝ) * (inp.mkWitnessData ce pds WSubs).τ₂ ≤
      (cntNew : ℝ) / (inp.mkWitnessData ce pds WSubs).wW eW) :
    rCur ≤ cntNew := by
  let wd := inp.mkWitnessData ce pds WSubs
  have hw_pos : 0 < wd.wW eW := mkW_wW_pos (hok (exists_localSpannerTools 0 0).some) hws heW
  have htwo := mkW_two_le_tau2_wW_comp hok hws hge heW
  have h1 : (rCur : ℝ) * 2 ≤ (rCur : ℝ) * (wd.τ₂ * wd.wW eW) :=
    mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg rCur)
  have h2 : (rCur : ℝ) * wd.τ₂ * wd.wW eW ≤ (cntNew : ℝ) := (le_div_iff₀ hw_pos).mp hle
  have h3 : (rCur : ℝ) ≤ (cntNew : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) rCur]
  exact_mod_cast h3

lemma t3_econgPhi_step_inc {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) {mem mem' : ℕ → ℕ} {eW : ℕ}
    (heW : eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m)
    (hcnt : mem' (lay.econgCountAddr + eW) = mem (lay.econgCountAddr + eW) + 1)
    (hcnt_other : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, eW' ≠ eW →
      mem' (lay.econgCountAddr + eW') = mem (lay.econgCountAddr + eW'))
    (hdel_eW : mem' (lay.wDelStampAddr + eW) = mem (lay.wDelStampAddr + eW))
    (hdel_other : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, eW' ≠ eW →
      mem' (lay.wDelStampAddr + eW') = mem (lay.wDelStampAddr + eW'))
    (hle : mem (lay.wDelStampAddr + eW) ≤ mem (lay.econgCountAddr + eW)) :
    t3EcongPhi ctx lay mem' = t3EcongPhi ctx lay mem + 1 := by
  unfold t3EcongPhi
  rw [← Finset.add_sum_erase _ _ heW, ← Finset.add_sum_erase _ _ heW]
  have hrest : ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW,
      (mem' (lay.econgCountAddr + x) - mem' (lay.wDelStampAddr + x)) =
      ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW,
        (mem (lay.econgCountAddr + x) - mem (lay.wDelStampAddr + x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rcases Finset.mem_erase.mp hx with ⟨hne, hmem⟩
    rw [hcnt_other x hmem hne, hdel_other x hmem hne]
  rw [hrest, hcnt, hdel_eW]; omega

lemma t3_econgPhi_step_stamp {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) {mem mem' : ℕ → ℕ} {rCur eW : ℕ}
    (heW : eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m)
    (hcnt_eW : mem' (lay.econgCountAddr + eW) = mem (lay.econgCountAddr + eW) + 1)
    (hcnt_other : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, eW' ≠ eW →
      mem' (lay.econgCountAddr + eW') = mem (lay.econgCountAddr + eW'))
    (hdel_eW : mem' (lay.wDelStampAddr + eW) = rCur)
    (hdel_other : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, eW' ≠ eW →
      mem' (lay.wDelStampAddr + eW') = mem (lay.wDelStampAddr + eW'))
    (hlt : mem (lay.wDelStampAddr + eW) < rCur)
    (hle : mem (lay.wDelStampAddr + eW) ≤ mem (lay.econgCountAddr + eW)) :
    t3EcongPhi ctx lay mem' ≤ t3EcongPhi ctx lay mem := by
  unfold t3EcongPhi
  rw [← Finset.add_sum_erase _ _ heW, ← Finset.add_sum_erase _ _ heW]
  have hrest : ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW,
      (mem' (lay.econgCountAddr + x) - mem' (lay.wDelStampAddr + x)) =
      ∑ x ∈ (Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m).erase eW,
        (mem (lay.econgCountAddr + x) - mem (lay.wDelStampAddr + x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rcases Finset.mem_erase.mp hx with ⟨hne, hmem⟩
    rw [hcnt_other x hmem hne, hdel_other x hmem hne]
  rw [hrest, hcnt_eW, hdel_eW]; omega

theorem t3CopyVert_ptriple {w : ℕ} {p : Program}
    {hOld hMid vertsPtr : ℕ} {P : Walk} {verts : List ℕ} (memInit regsInit : ℕ → ℕ)
    (hw1 : 1 < 2 ^ w) (_hOld_w : hOld + 2 + P.verts.length < 2 ^ w)
    (hMid_w : hMid + 2 + P.verts.length < 2 ^ w) (hverts_w : vertsPtr + verts.length < 2 ^ w)
    (hle_hm : hOld + (1 + P.verts.length + P.edges.length) ≤ hMid) (hVerts_hi : vertsPtr + verts.length ≤ hMid)
    (hVerts : ListAt memInit vertsPtr verts) (hWalk : WalkAt memInit hOld P)
    (hVert_lt : ∀ v ∈ P.verts, v < verts.length) (hv_len : P.verts.length < 2 ^ w) :
    let copyVert :=
      Stmt.seq (.assign 19 (t3Ld (.reg 11) (t3Add (.const 1) (.reg 18))))
        (Stmt.seq (.assign 20 (.load (t3Add (.reg 16) (.reg 19))))
          (t3St (.reg 13) (t3Add (.const 1) (.reg 18)) (.reg 20)))
    let stmt := t3ForRange 18 (.const 0) (.reg 14) copyVert
    let Pre := fun (st : State) (Φ : ℕ) =>
      Φ = 0 ∧ st.regs = regsInit ∧ st.regs 11 = hOld ∧ st.regs 13 = hMid ∧
      st.regs 14 = P.verts.length ∧ st.regs 16 = vertsPtr ∧
      (∀ a, a < hMid + 1 → st.mem a = memInit a) ∧
      (∀ a, hMid + 1 + P.verts.length ≤ a → st.mem a = memInit a)
    let Post := fun (st : State) (Φ : ℕ) =>
      Φ = 0 ∧ (∀ r ≤ 17, st.regs r = regsInit r) ∧
      (∀ i, (hi : i < P.verts.length) →
        st.mem (hMid + 1 + i) = verts.getD (P.verts[i]'hi) 0) ∧
      (∀ a, a < hMid + 1 → st.mem a = memInit a) ∧
      (∀ a, hMid + 1 + P.verts.length ≤ a → st.mem a = memInit a)
    PTriple w p Pre stmt (pNormalPost Post) (fun _ => P.verts.length * 31 + 7) := by
  intro copyVert stmt Pre Post
  let Inv : ℕ → State → ℕ → Prop := fun k st' Φ' =>
    Φ' = 0 ∧ (∀ r ≤ 17, st'.regs r = regsInit r) ∧ st'.regs 18 = k ∧ k ≤ P.verts.length ∧
    st'.regs 11 = hOld ∧ st'.regs 13 = hMid ∧ st'.regs 14 = P.verts.length ∧ st'.regs 16 = vertsPtr ∧
    (∀ i, i < k → ∀ (hi : i < P.verts.length), st'.mem (hMid + 1 + i) = verts.getD (P.verts[i]'hi) 0) ∧
    (∀ a, a < hMid + 1 → st'.mem a = memInit a) ∧
    (∀ a, hMid + 1 + P.verts.length ≤ a → st'.mem a = memInit a)
  have hloop := PTriple.forRange_const (w := w) (p := p) (P := Pre)
    (r := 18) (lo := .const 0) (hi := .reg 14) (body := copyVert) (Inv := Inv)
    22 0 P.verts.length (Nat.zero_le _) hw1 (fun _ => hv_len)
    (fun s Φ' ⟨hΦ, hrg, h11, h13, h14, h16, hlo, hhi⟩ =>
      ⟨Expr.eval_const (by omega), hΦ,
        fun r hr => by
          show Function.update s.regs 18 0 r = regsInit r
          rw [Function.update_of_ne (by omega), hrg],
        by show Function.update s.regs 18 0 18 = 0; exact Function.update_self _ _ _,
        Nat.zero_le _,
        by show Function.update s.regs 18 0 11 = hOld; rw [Function.update_of_ne (by decide), h11],
        by show Function.update s.regs 18 0 13 = hMid; rw [Function.update_of_ne (by decide), h13],
        by show Function.update s.regs 18 0 14 = P.verts.length; rw [Function.update_of_ne (by decide), h14],
        by show Function.update s.regs 18 0 16 = vertsPtr; rw [Function.update_of_ne (by decide), h16],
        fun _ hi _ => absurd hi (Nat.not_lt_zero _), hlo, hhi⟩)
    (fun _ _ _ _ _ h => h.2.2.1)
    (fun _ _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.2.2.2.2.1)
    (fun k _ hk s Φ' _ ⟨hΦ, hregs, hr18, _, hr11, hr13, hr14, hr16, hpref, hlo, hhi⟩ => by
      subst hΦ
      let vIdx := P.verts[k]'hk
      have hv_lt : vIdx < verts.length := hVert_lt vIdx (List.getElem_mem hk)
      have hm_vIdx : s.mem (hOld + (1 + k)) = vIdx := by
        have hlt_m : hOld + (1 + k) < hMid + 1 := by omega
        rw [hlo _ hlt_m]
        have hwv := (walkAt_iff.mp hWalk).2.1
        simpa [Nat.add_assoc] using listAt_getElem hwv hk
      have hm_val : s.mem (vertsPtr + vIdx) = verts.getD vIdx 0 := by
        rw [hlo _ (by omega), List.getD_eq_getElem _ _ hv_lt]
        exact listAt_getElem hVerts hv_lt
      let r1 := Function.update s.regs 19 vIdx
      let r2 := Function.update r1 20 (verts.getD vIdx 0)
      let mem' := Function.update s.mem (hMid + (1 + k)) (verts.getD vIdx 0)
      have hr1_16 : r1 16 = vertsPtr := by dsimp only [r1]; rw [Function.update_of_ne (by decide), hr16]
      have hr1_19 : r1 19 = vIdx := Function.update_self _ _ _
      have hr2_13 : r2 13 = hMid := by
        dsimp only [r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr13]
      have hr2_18 : r2 18 = k := by
        dsimp only [r2, r1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr18]
      have hr2_20 : r2 20 = verts.getD vIdx 0 := Function.update_self _ _ _
      have h1k_w : 1 + k < 2 ^ w := by omega
      have hOldk_w : hOld + (1 + k) < 2 ^ w := by omega
      have hvv_w : vertsPtr + vIdx < 2 ^ w := by omega
      have hMidk_w : hMid + (1 + k) < 2 ^ w := by omega
      have hev19 : (t3Ld (.reg 11) (t3Add (.const 1) (.reg 18))).eval w s = some vIdx :=
        hm_vIdx ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr11)
          (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq hr18) h1k_w) hOldk_w)
      have hev20 : (Expr.load (t3Add (.reg 16) (.reg 19))).eval w ⟨s.mem, r1, s.pos⟩ =
          some (verts.getD vIdx 0) :=
        hm_val ▸ Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr1_16) (Expr.eval_reg_of_eq hr1_19) hvv_w)
      apply t3_ptriple_of_cps
      refine t3_assign_cps (r := 19) hev19 ?_
      refine t3_assign_cps (r := 20) hev20 ?_
      refine ⟨.normal, ⟨mem', r2, s.pos⟩, 7, 0,
        runs_store_iff.mpr ⟨hMid + (1 + k), verts.getD vIdx 0,
          Expr.eval_add (Expr.eval_reg_of_eq hr2_13) (Expr.eval_add (Expr.eval_const hw1) (Expr.eval_reg_of_eq hr2_18) h1k_w) hMidk_w,
          Expr.eval_reg_of_eq hr2_20, rfl, rfl, by simp only [Expr.size, t3Add]⟩,
        ⟨⟨rfl,
          fun r hr => by
            show Function.update r2 18 (k + 1) r = regsInit r
            rw [Function.update_of_ne (by omega)]
            dsimp only [r2, r1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hregs r hr,
          by show Function.update r2 18 (k + 1) 18 = k + 1; exact Function.update_self _ _ _,
          by omega,
          by show Function.update r2 18 (k + 1) 11 = hOld; dsimp only [r2, r1]
             rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr11],
          by show Function.update r2 18 (k + 1) 13 = hMid
             rw [Function.update_of_ne (by decide), hr2_13],
          by show Function.update r2 18 (k + 1) 14 = P.verts.length; dsimp only [r2, r1]
             rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr14],
          by show Function.update r2 18 (k + 1) 16 = vertsPtr; dsimp only [r2, r1]
             rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_of_ne (by decide), hr16],
          fun i hi1 hi2 => by
            dsimp only [mem']
            by_cases hik : i = k
            · subst hik; rw [Nat.add_assoc, Function.update_self]
            · rw [Function.update_of_ne (by omega)]; exact hpref i (by omega) hi2,
          fun a ha => by dsimp only [mem']; rw [Function.update_of_ne (by omega)]; exact hlo a ha,
          fun a ha => by dsimp only [mem']; rw [Function.update_of_ne (by omega)]; exact hhi a ha⟩,
          hr2_18⟩,
        by simp only [Expr.size, t3Ld, t3Add]; omega⟩)
  exact hloop.conseq (fun _ _ h => h)
    (fun o st' Φ' hq => by
      cases o with
      | returned _ => exact False.elim hq
      | normal =>
        rcases hq with ⟨hΦ, hregs, _, _, _, _, _, _, hpref, hlo, hhi⟩
        exact ⟨hΦ, hregs, fun i hi => hpref i hi hi, hlo, hhi⟩)
    (fun _ => by simp only [Expr.size, Nat.sub_zero]; omega)

structure T3EdgeStepInv {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ} {w : ℕ}
    (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (rCur eJ ci : ℕ) (hci : ci < ctx.wd.comps.length)
    (hOld hMid : ℕ) (P : Walk) (d0 : T3RoundData impl.pathDS) (reps1 : ℕ → impl.pathDS.R.τ)
    (memStart regsInit : ℕ → ℕ) (k : ℕ) (st : State) (Φ : ℕ) : Prop where
  k_le : k ≤ P.edges.length
  regs_hi : ∀ r ≤ 24, r ≠ 18 → st.regs r = regsInit r
  reg_25 : st.regs 25 = k
  mem_agree : ∀ a,
    a ≠ lay.base + t3OffEcongUpd →
    ¬ (lay.econgCountAddr ≤ a ∧ a < lay.econgCountAddr + ctx.wd.W.m) →
    ¬ (lay.wDelStampAddr ≤ a ∧ a < lay.wDelStampAddr + ctx.wd.W.m) →
    ¬ (lay.queueAddr ≤ a ∧ a < lay.queueAddr + P.edges.length) →
    ¬ (hMid + 2 + P.verts.length ≤ a ∧ a < hMid + 2 + P.verts.length + P.edges.length) →
    st.mem a = memStart a
  wdel_j0 : ∀ eW < ctx.wd.j0Edges.length, st.mem (lay.wDelStampAddr + eW) = memStart (lay.wDelStampAddr + eW)
  econgUpd_eq : st.mem (lay.base + t3OffEcongUpd) = d0.econgUpd + k
  walk_edges_eq : ∀ i, i < k → ∀ (hi : i < P.edges.length),
    st.mem (hMid + 2 + P.verts.length + i) = ctx.wd.comps[ci].wStart + P.edges[i]'hi
  exists_Q : ∃ Q : List ℕ,
    let P_lift := liftWSubWalk ctx.wd.comps[ci] P
    let embk : ℕ → Option Walk := Function.update d0.emb eJ (some ⟨P_lift.verts, P_lift.edges.take k⟩)
    st.regs 18 = Q.length ∧
    Q.length ≤ k ∧
    Q.Nodup ∧
    ListAt st.mem lay.queueAddr Q ∧
    (∀ eW ∈ Q, (∃ j < k, ∃ hj : j < P_lift.edges.length, P_lift.edges[j]'hj = eW) ∧
      ctx.wd.j0Edges.length ≤ eW ∧ eW < ctx.wd.W.m ∧ st.mem (lay.wDelStampAddr + eW) = rCur) ∧
    (∀ eW < ctx.wd.W.m, st.mem (lay.econgCountAddr + eW) =
      {j ∈ Finset.range inp.J.m | eW ∈ (partialToWalk embk j).edges}.card) ∧
    (∀ eW < ctx.wd.W.m, econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk embk) eW ≤
      ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂) ∧
    (∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      st.mem (lay.wDelStampAddr + eW) ≤ rCur ∧
      st.mem (lay.wDelStampAddr + eW) ≤ st.mem (lay.econgCountAddr + eW)) ∧
    (∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      st.mem (lay.wDelStampAddr + eW) = rCur →
      (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk embk) eW) ∧
    (∀ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      st.mem (lay.wDelStampAddr + eW) < rCur →
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk embk) eW ≤ (rCur : ℝ) * ctx.wd.τ₂) ∧
    d0.econgUpd + k = ∑ eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      st.mem (lay.econgCountAddr + eW) ∧
    (∀ (cj : ℕ) (hcj : cj < ctx.wd.comps.length) (eL : ℕ), eL < ctx.wd.comps[cj].W_sub.m →
      (eL ∈ (d0.states cj).deleted ↔
        st.mem (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL)) = rCur ∧
        (ctx.wd.comps[cj].wStart + eL) ∉ Q)) ∧
    Φ = t3KdelCost impl inp.J * (t3EcongPhi ctx lay st.mem + Q.length + (P.edges.length - k)) +
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 st.mem +
      25 * t3VhatRem ctx.wd d0.states

lemma t3EdgeStep_addr_disjoint {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {hOld hMid eW k : ℕ} {P : Walk} (hOld_lo : lay.staticEnd ≤ hOld) (hle_hm : hOld + (1 + P.verts.length + P.edges.length) ≤ hMid)
    (hPe_le : P.edges.length ≤ ctx.wd.W.m) (hk : k < P.edges.length) (heW_lt : eW < ctx.wd.W.m) :
    let wWNumAddr := ctx.memT1 (ctx.wInp.h + 14)
    let hBase := hMid + 2 + P.verts.length
    wWNumAddr + eW < lay.staticEnd ∧
    lay.econgCountAddr + eW ≠ lay.base + t3OffEcongUpd ∧
    lay.wDelStampAddr + eW ≠ lay.base + t3OffEcongUpd ∧
    lay.queueAddr + k ≠ lay.base + t3OffEcongUpd ∧
    hBase + k ≠ lay.base + t3OffEcongUpd ∧
    (hOld + 2 + P.verts.length + k < lay.staticEnd → False) ∧
    lay.staticEnd ≤ hBase ∧
    lay.econgCountAddr + ctx.wd.W.m ≤ lay.wDelStampAddr ∧
    lay.wDelStampAddr + ctx.wd.W.m ≤ lay.queueAddr ∧
    lay.queueAddr + P.edges.length ≤ lay.vhatOffsetAddr ∧
    lay.vhatOffsetAddr ≤ lay.staticEnd ∧
    lay.base + t3OffEta2 < lay.econgCountAddr ∧
    lay.base + t3OffEcongUpd < lay.econgCountAddr := by
  have hb := T3Layout.bounds ctx
  have ho := ctx.outAt
  rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, halo, haw, hwn, hws_eq, hjs_eq, hv1_eq, _⟩
  have hlt1 := ctx.lt_v1_of_t1
  have hv1 := ctx.hv1_le
  have hvm : ctx.wInp.prep.J.m = inp.J.m := by rw [ctx.hWInpJ]
  subst hlay
  unfold t3OffEta2 t3OffEcongUpd t3HdrSize at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, fun h => by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

private lemma t3EdgeStep_mem5_from3 {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {pe eW rCur Qlen : ℕ} (mem3 : ℕ → ℕ)
    (hPe_le : pe ≤ ctx.wd.W.m) (hQ_lt : Qlen < pe) (heW : eW < ctx.wd.W.m) :
    let mem4 := Function.update mem3 (lay.wDelStampAddr + eW) rCur
    let mem5 := Function.update mem4 (lay.queueAddr + Qlen) eW
    (∀ eW' < ctx.wd.W.m, mem5 (lay.econgCountAddr + eW') = mem3 (lay.econgCountAddr + eW')) ∧
    (∀ eW' < ctx.wd.W.m, eW' ≠ eW → mem5 (lay.wDelStampAddr + eW') = mem3 (lay.wDelStampAddr + eW')) ∧
    mem5 (lay.wDelStampAddr + eW) = rCur ∧
    (∀ i < Qlen, mem5 (lay.queueAddr + i) = mem3 (lay.queueAddr + i)) ∧
    mem5 (lay.queueAddr + Qlen) = eW ∧
    (∀ cj < ctx.wd.comps.length, mem5 (lay.dsHandlesAddr + cj) = mem3 (lay.dsHandlesAddr + cj)) ∧
    (∀ a, lay.staticEnd ≤ a → mem5 a = mem3 a) ∧
    (∀ a, ¬ (lay.wDelStampAddr ≤ a ∧ a < lay.wDelStampAddr + ctx.wd.W.m) →
      ¬ (lay.queueAddr ≤ a ∧ a < lay.queueAddr + pe) → mem5 a = mem3 a) := by
  have hb := T3Layout.bounds ctx; subst hlay; intro mem4 mem5
  refine ⟨fun eW' _ => ?_, fun eW' _ hne => ?_, ?_, fun i hi => ?_, ?_, fun cj hcj => ?_,
    fun a ha => ?_, fun a h1 h2 => ?_⟩
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_self]
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · exact Function.update_self _ _ _
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem5, mem4]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  · dsimp only [mem5, mem4]
    rw [Function.update_of_ne (fun heq => h2 (by omega)), Function.update_of_ne (fun heq => h1 (by omega))]

lemma t3EdgeStep_push_branch {impl : SpannerToolImpl} {inp : Task3Input} {mem₀ : ℕ → ℕ}
    {w : ℕ} (ctx : T3Ctx impl inp mem₀ w) (lay : T3Layout) (hlay : lay = T3Layout.ofCtx ctx)
    {p : Program} {rCur eJ ci : ℕ} (hci : ci < ctx.wd.comps.length)
    {hOld hMid : ℕ} {P : Walk} (d0 : T3RoundData impl.pathDS) (reps1 : ℕ → impl.pathDS.R.τ)
    (memStart regsInit sMem mem3 r30 : ℕ → ℕ) {ω' : ℕ → Bool} {pos k Φ' uL vL cntNew : ℕ} (Q : List ℕ)
    (hk : k < P.edges.length) (hPe_le_Wm : P.edges.length ≤ ctx.wd.W.m)
    (hPl_len : k < (liftWSubWalk ctx.wd.comps[ci] P).edges.length) (hMid_lo : lay.staticEnd ≤ hMid)
    (hP_wk : P.IsWalk ctx.wd.comps[ci].W_sub uL vL) (hP_ndel : ∀ e ∈ P.edges, e ∉ (d0.states ci).deleted)
    (hw1 : 1 < 2 ^ w) (hwdel_add_w : lay.wDelStampAddr + (ctx.wd.comps[ci].wStart + P.edges[k]'hk) < 2 ^ w)
    (hq_add_w : lay.queueAddr + Q.length < 2 ^ w) (hqLen_w : Q.length + 1 < 2 ^ w)
    (hQk : Q.length ≤ k) (hQnd : Q.Nodup) (hQL : ListAt sMem lay.queueAddr Q)
    (hQval : ∀ e' ∈ Q, (∃ j < k, ∃ hj : j < (liftWSubWalk ctx.wd.comps[ci] P).edges.length,
        (liftWSubWalk ctx.wd.comps[ci] P).edges[j]'hj = e') ∧
      ctx.wd.j0Edges.length ≤ e' ∧ e' < ctx.wd.W.m ∧ sMem (lay.wDelStampAddr + e') = rCur)
    (heW_lo : ctx.wd.j0Edges.length ≤ ctx.wd.comps[ci].wStart + P.edges[k]'hk)
    (heW_hi : ctx.wd.comps[ci].wStart + P.edges[k]'hk < ctx.wd.W.m)
    (heW_not_Q : ctx.wd.comps[ci].wStart + P.edges[k]'hk ∉ Q)
    (heW_lt_r : sMem (lay.wDelStampAddr + (ctx.wd.comps[ci].wStart + P.edges[k]'hk)) < rCur)
    (hr30_hi : ∀ r ≤ 24, r ≠ 18 → r30 r = regsInit r) (hr30_25 : r30 25 = k)
    (hr30_1 : r30 1 = rCur) (hr30_18 : r30 18 = Q.length)
    (hr30_23 : r30 23 = lay.wDelStampAddr) (hr30_24 : r30 24 = lay.queueAddr)
    (hr30_27 : r30 27 = ctx.wd.comps[ci].wStart + P.edges[k]'hk)
    (hev_cond : (t3Lt (.reg 30) (.reg 29)).eval w ⟨mem3, r30, pos⟩ = some 0)
    (hm3_agree : ∀ a, a ≠ lay.base + t3OffEcongUpd →
      ¬ (lay.econgCountAddr ≤ a ∧ a < lay.econgCountAddr + ctx.wd.W.m) →
      ¬ (lay.wDelStampAddr ≤ a ∧ a < lay.wDelStampAddr + ctx.wd.W.m) →
      ¬ (lay.queueAddr ≤ a ∧ a < lay.queueAddr + P.edges.length) →
      ¬ (hMid + 2 + P.verts.length ≤ a ∧ a < hMid + 2 + P.verts.length + P.edges.length) →
      mem3 a = memStart a)
    (hs_wdel_j0 : ∀ eW' < ctx.wd.j0Edges.length, sMem (lay.wDelStampAddr + eW') = memStart (lay.wDelStampAddr + eW'))
    (hm3_eUpd : mem3 (lay.base + t3OffEcongUpd) = d0.econgUpd + k + 1)
    (hm3_we : ∀ i < k + 1, ∀ (hi : i < P.edges.length), mem3 (hMid + 2 + P.verts.length + i) = ctx.wd.comps[ci].wStart + P.edges[i]'hi)
    (hm3_q : ∀ i < k, mem3 (lay.queueAddr + i) = sMem (lay.queueAddr + i))
    (hm3_wdel : ∀ eW' < ctx.wd.W.m, mem3 (lay.wDelStampAddr + eW') = sMem (lay.wDelStampAddr + eW'))
    (hm3_cnt : ∀ eW' < ctx.wd.W.m, eW' ≠ ctx.wd.comps[ci].wStart + P.edges[k]'hk →
      mem3 (lay.econgCountAddr + eW') = sMem (lay.econgCountAddr + eW'))
    (hm3_eW : mem3 (lay.econgCountAddr + (ctx.wd.comps[ci].wStart + P.edges[k]'hk)) = cntNew)
    (hm3_eW_inc : mem3 (lay.econgCountAddr + (ctx.wd.comps[ci].wStart + P.edges[k]'hk)) =
      sMem (lay.econgCountAddr + (ctx.wd.comps[ci].wStart + P.edges[k]'hk)) + 1)
    (hcnt3_eq : ∀ eW' < ctx.wd.W.m, mem3 (lay.econgCountAddr + eW') =
      {j ∈ Finset.range inp.J.m | eW' ∈ (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take (k + 1)⟩)) j).edges}.card)
    (hecong_new_eq : ∀ eW' < ctx.wd.W.m, eW' ≠ ctx.wd.comps[ci].wStart + P.edges[k]'hk →
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take (k + 1)⟩))) eW' =
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take k⟩))) eW')
    (hm_new_rnd : econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take (k + 1)⟩)))
        (ctx.wd.comps[ci].wStart + P.edges[k]'hk) ≤ ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂)
    (hge_thresh : (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take (k + 1)⟩)))
        (ctx.wd.comps[ci].wStart + P.edges[k]'hk))
    (hr_le_cnt : rCur ≤ cntNew)
    (hEc_r : ∀ eW' < ctx.wd.W.m, econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take k⟩))) eW' ≤ ((rCur : ℝ) + 1 / 2) * ctx.wd.τ₂)
    (hWdc : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m,
      sMem (lay.wDelStampAddr + eW') ≤ rCur ∧ sMem (lay.wDelStampAddr + eW') ≤ sMem (lay.econgCountAddr + eW'))
    (hWdt : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, sMem (lay.wDelStampAddr + eW') = rCur →
      (rCur : ℝ) * ctx.wd.τ₂ ≤ econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take k⟩))) eW')
    (hWdlt : ∀ eW' ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, sMem (lay.wDelStampAddr + eW') < rCur →
      econgAt inp.J (fun _ => 1) ctx.wd.wW (partialToWalk
        (Function.update d0.emb eJ (some ⟨(liftWSubWalk ctx.wd.comps[ci] P).verts,
          (liftWSubWalk ctx.wd.comps[ci] P).edges.take k⟩))) eW' ≤ (rCur : ℝ) * ctx.wd.τ₂)
    (hUsum3 : d0.econgUpd + (k + 1) = ∑ x ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m, mem3 (lay.econgCountAddr + x))
    (hDQ : ∀ (cj : ℕ) (hcj : cj < ctx.wd.comps.length) (eL' : ℕ), eL' < ctx.wd.comps[cj].W_sub.m →
      (eL' ∈ (d0.states cj).deleted ↔
        sMem (lay.wDelStampAddr + (ctx.wd.comps[cj].wStart + eL')) = rCur ∧ (ctx.wd.comps[cj].wStart + eL') ∉ Q))
    (hds_fn : ∀ (mA : ℕ → ℕ), (∀ a, lay.staticEnd ≤ a → mA a = mem3 a) →
      (∀ cj < ctx.wd.comps.length, mA (lay.dsHandlesAddr + cj) = mem3 (lay.dsHandlesAddr + cj)) →
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mA =
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 sMem)
    (hΦ : Φ' = t3KdelCost impl inp.J * (t3EcongPhi ctx lay sMem + Q.length + (P.edges.length - k)) +
      dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 sMem + 25 * t3VhatRem ctx.wd d0.states) :
    ∃ o stF c_c Φ'',
      Runs w p ω' (.cond (t3Lt (.reg 30) (.reg 29)) .nop
        (.cond (t3Lt (.load (t3Add (.reg 23) (.reg 27))) (.reg 1))
          (Stmt.seq (.store (t3Add (.reg 23) (.reg 27)) (.reg 1))
            (Stmt.seq (.store (t3Add (.reg 24) (.reg 18)) (.reg 27))
              (.assign 18 (t3Add (.reg 18) (.const 1))))) .nop)) ⟨mem3, r30, pos⟩ o stF c_c ∧
      (o = .normal ∧ T3EdgeStepInv ctx lay rCur eJ ci hci hOld hMid P d0 reps1 memStart regsInit (k + 1)
        { stF with regs := Function.update stF.regs 25 (k + 1) } Φ'' ∧ stF.regs 25 = k) ∧
      c_c + Φ'' ≤ 31 + Φ' := by
  let P_lift := liftWSubWalk ctx.wd.comps[ci] P
  let eL := P.edges[k]'hk
  let eW := ctx.wd.comps[ci].wStart + eL
  have heW_eq : P_lift.edges[k]'hPl_len = eW := by simp [P_lift, liftWSubWalk, eL, eW]
  have heW_Ico : eW ∈ Finset.Ico ctx.wd.j0Edges.length ctx.wd.W.m := Finset.mem_Ico.mpr ⟨heW_lo, heW_hi⟩
  let mem4 := Function.update mem3 (lay.wDelStampAddr + eW) rCur
  let mem5 := Function.update mem4 (lay.queueAddr + Q.length) eW
  let r31 := Function.update r30 18 (Q.length + 1)
  have hm5p := t3EdgeStep_mem5_from3 ctx lay hlay (rCur := rCur) (Qlen := Q.length)
    mem3 hPe_le_Wm (by omega) heW_hi
  have hm5_cnt : ∀ eW' < ctx.wd.W.m, mem5 (lay.econgCountAddr + eW') = mem3 (lay.econgCountAddr + eW') := hm5p.1
  have hm5_wdel : ∀ eW' < ctx.wd.W.m, eW' ≠ eW → mem5 (lay.wDelStampAddr + eW') = mem3 (lay.wDelStampAddr + eW') := hm5p.2.1
  have hm5_wdel_self : mem5 (lay.wDelStampAddr + eW) = rCur := hm5p.2.2.1
  have hm5_q : ∀ i < Q.length, mem5 (lay.queueAddr + i) = mem3 (lay.queueAddr + i) := hm5p.2.2.2.1
  have hm5_q_self : mem5 (lay.queueAddr + Q.length) = eW := hm5p.2.2.2.2.1
  have hm5_eUpd : mem5 (lay.base + t3OffEcongUpd) = d0.econgUpd + k + 1 :=
    (hm5p.2.2.2.2.2.2.2 _ (by have := T3Layout.bounds ctx; subst hlay; unfold t3OffEcongUpd t3HdrSize at *; omega)
      (by have := T3Layout.bounds ctx; subst hlay; unfold t3OffEcongUpd t3HdrSize at *; omega)).trans hm3_eUpd
  have hm3_wdel_self : mem3 (lay.wDelStampAddr + eW) < rCur := (hm3_wdel eW heW_hi).symm ▸ heW_lt_r
  have hev_cond2 : (t3Lt (.load (t3Add (.reg 23) (.reg 27))) (.reg 1)).eval w ⟨mem3, r30, pos⟩ = some 1 :=
    (congrArg some (ite_eq_left_iff.mpr fun h => absurd hm3_wdel_self h)) ▸
      Expr.eval_lt_op (Expr.eval_load (Expr.eval_add (Expr.eval_reg_of_eq hr30_23) (Expr.eval_reg_of_eq hr30_27) hwdel_add_w))
        (Expr.eval_reg_of_eq hr30_1) hw1
  have hev_inc : (t3Add (.reg 18) (.const 1)).eval w ⟨mem5, r30, pos⟩ = some (Q.length + 1) :=
    Expr.eval_add (Expr.eval_reg_of_eq hr30_18) (Expr.eval_const hw1) hqLen_w
  have hruns_c2 : Runs w p ω'
      (.cond (t3Lt (.load (t3Add (.reg 23) (.reg 27))) (.reg 1))
        (Stmt.seq (.store (t3Add (.reg 23) (.reg 27)) (.reg 1))
          (Stmt.seq (.store (t3Add (.reg 24) (.reg 18)) (.reg 27)) (.assign 18 (t3Add (.reg 18) (.const 1))))) .nop)
      ⟨mem3, r30, pos⟩ .normal ⟨mem5, r31, pos⟩ 23 := by
    refine runs_cond_iff.mpr ⟨1, 16, hev_cond2, ?_, by simp [Expr.size, t3Lt, t3Add]⟩
    refine runs_seq_iff.mpr (Or.inr ⟨⟨mem4, r30, pos⟩, 5, 10,
      runs_store_iff.mpr ⟨_, rCur, Expr.eval_add (Expr.eval_reg_of_eq hr30_23) (Expr.eval_reg_of_eq hr30_27) hwdel_add_w,
        Expr.eval_reg_of_eq hr30_1, rfl, rfl, by simp [Expr.size, t3Add]⟩,
      runs_seq_iff.mpr (Or.inr ⟨⟨mem5, r30, pos⟩, 5, 4,
        runs_store_iff.mpr ⟨_, eW, Expr.eval_add (Expr.eval_reg_of_eq hr30_24) (Expr.eval_reg_of_eq hr30_18) hq_add_w,
          Expr.eval_reg_of_eq hr30_27, rfl, rfl, by simp [Expr.size, t3Add]⟩,
        runs_assign_iff.mpr ⟨Q.length + 1, hev_inc, rfl, rfl, by simp [Expr.size, t3Add]⟩, rfl⟩), rfl⟩)
  have hds_m5 := hds_fn mem5 hm5p.2.2.2.2.2.2.1 hm5p.2.2.2.2.2.1
  have hePhi5 : t3EcongPhi ctx lay mem5 ≤ t3EcongPhi ctx lay sMem :=
    t3_econgPhi_step_stamp ctx lay heW_Ico ((hm5_cnt eW heW_hi).trans hm3_eW_inc)
      (fun eW' heW' hne => (hm5_cnt eW' (Finset.mem_Ico.mp heW').2).trans (hm3_cnt eW' (Finset.mem_Ico.mp heW').2 hne))
      hm5_wdel_self
      (fun eW' heW' hne => (hm5_wdel eW' (Finset.mem_Ico.mp heW').2 hne).trans (hm3_wdel eW' (Finset.mem_Ico.mp heW').2))
      heW_lt_r (hWdc eW heW_Ico).2
  let Φ5 := t3KdelCost impl inp.J * (t3EcongPhi ctx lay mem5 + (Q ++ [eW]).length + (P.edges.length - (k + 1))) +
    dsTotalPhi impl.pathDS lay.dsHandlesAddr ctx.wd.comps.length reps1 mem5 + 25 * t3VhatRem ctx.wd d0.states
  refine ⟨.normal, ⟨mem5, r31, pos⟩, 27, Φ5, runs_cond_iff.mpr ⟨0, 23, hev_cond, hruns_c2, by simp [Expr.size, t3Lt]⟩,
    ⟨rfl, ⟨hk,
      fun r hr h18 => by show Function.update r31 25 (k + 1) r = regsInit r; rw [Function.update_of_ne (by omega)]; dsimp only [r31]; rw [Function.update_of_ne (by omega)]; exact hr30_hi r hr h18,
      by show Function.update r31 25 (k + 1) 25 = k + 1; exact Function.update_self _ _ _,
      fun a h1 h2 h3 h4 h5 => (hm5p.2.2.2.2.2.2.2 a h3 h4).trans (hm3_agree a h1 h2 h3 h4 h5),
      fun eW' heW' => (hm5_wdel eW' (by omega) (by omega)).trans ((hm3_wdel eW' (by omega)).trans (hs_wdel_j0 eW' heW')),
      hm5_eUpd, fun i hi1 hi2 => (hm5p.2.2.2.2.2.2.1 _ (by omega)).trans (hm3_we i hi1 hi2),
      Q ++ [eW], by show Function.update r31 25 (k + 1) 18 = (Q ++ [eW]).length; rw [Function.update_of_ne (by decide)]; simp [r31],
      by simp; omega,
      List.nodup_append.mpr ⟨hQnd, List.nodup_singleton eW, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; intro h; subst h; exact heW_not_Q ha⟩,
      fun i hi => by
        rw [List.length_append, List.length_singleton] at hi
        by_cases hik : i < Q.length
        · rw [List.getElem_append_left hik]; exact (hm5_q i hik).trans ((hm3_q i (by omega)).trans (hQL i hik))
        · have hieq : i = Q.length := by omega
          subst hieq; simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton]; exact hm5_q_self,
      fun e' he' => by
        rw [List.mem_append, List.mem_singleton] at he'
        rcases he' with he' | rfl
        · have hq := hQval e' he'; rcases hq.1 with ⟨j, hj1, hj2, hj3⟩
          exact ⟨⟨j, by omega, hj2, hj3⟩, hq.2.1, hq.2.2.1, by
            by_cases heq : e' = eW
            · subst heq; exact absurd he' heW_not_Q
            · exact (hm5_wdel e' hq.2.2.1 heq).trans ((hm3_wdel e' hq.2.2.1).trans hq.2.2.2)⟩
        · exact ⟨⟨k, Nat.lt_succ_self k, hPl_len, heW_eq⟩, heW_lo, heW_hi, hm5_wdel_self⟩,
      fun eW' heW' => (hm5_cnt eW' heW').trans (hcnt3_eq eW' heW'),
      fun eW' heW' => by
        by_cases h : eW' = eW
        · subst h; exact hm_new_rnd
        · rw [hecong_new_eq eW' heW' h]; exact hEc_r eW' heW',
      fun eW' heW' => by
        dsimp only
        by_cases h : eW' = eW
        · subst h; rw [hm5_wdel_self, hm5_cnt eW heW_hi, hm3_eW]; exact ⟨le_refl _, hr_le_cnt⟩
        · let he := Finset.mem_Ico.mp heW'; rw [hm5_wdel eW' he.2 h, hm3_wdel eW' he.2, hm5_cnt eW' he.2, hm3_cnt eW' he.2 h]; exact hWdc eW' heW',
      fun eW' heW' hs => by
        dsimp only at hs
        by_cases h : eW' = eW
        · subst h; exact hge_thresh
        · rw [hm5_wdel eW' (Finset.mem_Ico.mp heW').2 h, hm3_wdel eW' (Finset.mem_Ico.mp heW').2] at hs
          rw [hecong_new_eq eW' (Finset.mem_Ico.mp heW').2 h]; exact hWdt eW' heW' hs,
      fun eW' heW' hlt' => by
        dsimp only at hlt'
        by_cases h : eW' = eW
        · subst h; rw [hm5_wdel_self] at hlt'; exact absurd hlt' (lt_irrefl rCur)
        · rw [hm5_wdel eW' (Finset.mem_Ico.mp heW').2 h, hm3_wdel eW' (Finset.mem_Ico.mp heW').2] at hlt'
          rw [hecong_new_eq eW' (Finset.mem_Ico.mp heW').2 h]; exact hWdlt eW' heW' hlt',
      by dsimp only; rw [hUsum3]; exact Finset.sum_congr rfl fun x hx => (hm5_cnt x (Finset.mem_Ico.mp hx).2).symm,
      fun cj hcj eL' heL' => by
        let eW' := ctx.wd.comps[cj].wStart + eL'
        have hc_b := (ctx.hw_okW.comp_props cj hcj).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        dsimp only
        by_cases heq : eW' = eW
        · have hinj := wStart_add_inj ctx hcj hci heL' (by
            rcases hP_wk with ⟨_, _, ⟨_, hee, _⟩ | ⟨_, _, _, _, hlt', _⟩⟩
            · rw [hee] at hk; simp at hk
            · exact hlt' eL (List.getElem_mem hk)) heq
          rcases hinj with ⟨rfl, rfl⟩
          exact ⟨fun h => absurd h (hP_ndel eL (List.getElem_mem hk)),
            fun h => absurd (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))) h.2⟩
        · rw [hm5_wdel eW' (Nat.lt_of_lt_of_le (Nat.add_lt_add_left heL' _) hc_b.2) heq,
            hm3_wdel eW' (Nat.lt_of_lt_of_le (Nat.add_lt_add_left heL' _) hc_b.2)]
          exact ⟨fun h => let hw := (hDQ cj hcj eL' heL').mp h; ⟨hw.1, fun hm => hw.2 ((List.mem_append.mp hm).elim id fun hs => absurd (List.mem_singleton.mp hs) heq)⟩,
            fun ⟨h1, h2⟩ => (hDQ cj hcj eL' heL').mpr ⟨h1, fun hm => h2 (List.mem_append.mpr (Or.inl hm))⟩⟩,
      rfl⟩, by show Function.update r30 18 (Q.length + 1) 25 = k; rw [Function.update_of_ne (by decide)]; exact hr30_25⟩,
    by
      have hkp : P.edges.length - (k + 1) + 1 = P.edges.length - k := by omega
      have hdrop : t3EcongPhi ctx lay mem5 + (Q ++ [eW]).length + (P.edges.length - (k + 1)) ≤
          t3EcongPhi ctx lay sMem + Q.length + (P.edges.length - k) := by
        rw [List.length_append, List.length_singleton]; linarith [hePhi5]
      have hmul_le := Nat.mul_le_mul_left (t3KdelCost impl inp.J) hdrop
      dsimp only [Φ5]; rw [hds_m5, hΦ]
      exact Nat.add_le_add (by decide) (Nat.add_le_add_right (Nat.add_le_add_right hmul_le _) _)⟩

end MinCostFlow.Spanner
