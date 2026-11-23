module

public import MinCostFlow.Spanner.ProgComposeWalkProof

@[expose] public section

/-!
# Writing a Composed Embedding

The embedding of `J` into `J̃` is `compose W embWJtilde embJW`: for each edge `e` of `J`, the
walk `embJW e` in `W` is turned into a walk in `J̃` by `composeWalkBody`. This file gives the loop
over the edges of `J`. It writes a pointer table and then the walks one after the other, as in
`mapEmbBody`. The result is `composeEmb_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- Procedure body, at `args = [bAddr, E, EA, m, dst, S, VB, EB, L, K]`; `fw` holds
`composeWalkBody`. The last argument is used only by the contract. -/
def composeEmbBody (fw : ℕ) : Stmt :=
  .assign 14 (.bin .add (.reg 4) (.reg 3)) ;;
  forRange 13 (.const 0) (.reg 3) (
    .assign 12 (.load (.bin .add (.reg 2) (.reg 13))) ;;
    .store (.bin .add (.reg 4) (.reg 13)) (.reg 14) ;;
    .call 15 fw [.reg 0, .reg 1, .reg 12, .reg 14, .reg 5, .reg 6, .reg 7, .reg 8] ;;
    .assign 16 (.load (.reg 14)) ;;
    .assign 17 (.load (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))) ;;
    .assign 14 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 2)) (.reg 16)) (.reg 17))) ;;
  .ret (.const 0)

/-- The graph `B`, its embedding `embBC`, and the embedding `embAB` of `m` edges are stored
below the scratch area `S`. Each walk of `embAB` has at most `K` edges. The scratch area, the two
buffers and the output follow one another, and the output fits in a word. -/
def ComposeEmbPre (mem : ℕ → ℕ) (bAddr E EA m dst S VB EB L K : ℕ) (B : Graph)
    (embBC embAB : ℕ → Walk) (w : ℕ) : Prop :=
  GraphAt mem bAddr B ∧ EmbAt mem E B.m embBC ∧ EmbBounded mem E B.m embBC S ∧
    bAddr + (2 + 2 * B.m) ≤ S ∧ EmbAt mem EA m embAB ∧ EmbBounded mem EA m embAB S ∧
    (∀ e < m, (embAB e).verts.length = (embAB e).edges.length + 1 ∨
      ((embAB e).verts = [] ∧ (embAB e).edges = [])) ∧
    (∀ e < m, ∀ j ∈ (embAB e).edges, j < B.m) ∧ (∀ e < m, ∀ x ∈ (embAB e).verts, x < 2 ^ w) ∧
    (∀ e < m, (embAB e).edges.length ≤ K) ∧
    (∀ j < B.m, (Walk.encode (embBC j)).length ≤ L) ∧
    (∀ j < B.m, (embBC j).edges ≠ [] → (embBC j).verts ≠ []) ∧
    S + L ≤ VB ∧ VB + K * L ≤ EB ∧ EB + K * L ≤ dst ∧
    dst + m + m * (2 + 2 * (K * L)) < 2 ^ w ∧ 1 < 2 ^ w

/-- Contract of `composeEmbBody`. -/
def composeEmbContract (w : ℕ) : Contract where
  pre args mem := ∃ bAddr E EA m dst S VB EB L K B embBC embAB,
    args = [bAddr, E, EA, m, dst, S, VB, EB, L, K] ∧
    ComposeEmbPre mem bAddr E EA m dst S VB EB L K B embBC embAB w
  post args mem _ mem' := ∀ bAddr E EA m dst S VB EB L K B embBC embAB,
    args = [bAddr, E, EA, m, dst, S, VB, EB, L, K] →
    ComposeEmbPre mem bAddr E EA m dst S VB EB L K B embBC embAB w →
    EmbAt mem' dst m (compose B embBC embAB) ∧
      EmbBounded mem' dst m (compose B embBC embAB)
        (dst + m + embOffs (compose B embBC embAB) m) ∧
      (∀ e < m, dst ≤ mem' (dst + e)) ∧
      ∀ x, x < S ∨ dst + m + embOffs (compose B embBC embAB) m ≤ x → mem' x = mem x
  cost args _ := args.getD 3 0 * (args.getD 9 0 * (120 * args.getD 8 0 + 620) + 300) + 30

/-- Loop invariant after `k` walks. -/
def CEInv (mem : ℕ → ℕ) (bAddr E EA m dst S VB EB L K : ℕ) (B : Graph)
    (embBC embAB : ℕ → Walk) (k : ℕ) (st : State) : Prop :=
  st.regs 0 = bAddr ∧ st.regs 1 = E ∧ st.regs 2 = EA ∧ st.regs 3 = m ∧ st.regs 4 = dst ∧
    st.regs 5 = S ∧ st.regs 6 = VB ∧ st.regs 7 = EB ∧ st.regs 8 = L ∧ st.regs 13 = k ∧
    st.regs 14 = dst + m + embOffs (compose B embBC embAB) k ∧ k ≤ m ∧
    embOffs (compose B embBC embAB) k ≤ k * (2 + 2 * (K * L)) ∧
    (∀ t < k, st.mem (dst + t) = dst + m + embOffs (compose B embBC embAB) t ∧
      WalkAt st.mem (dst + m + embOffs (compose B embBC embAB) t) (compose B embBC embAB t)) ∧
    ∀ x, x < S ∨ dst + m + embOffs (compose B embBC embAB) k ≤ x → st.mem x = mem x

lemma composeEmb_step {w : ℕ} {p : Program} {fw : ℕ}
    (hfw : MeetsContract w p fw (composeWalkContract w))
    {mem : ℕ → ℕ} {bAddr E EA m dst S VB EB L K : ℕ} {B : Graph} {embBC embAB : ℕ → Walk}
    (hpre : ComposeEmbPre mem bAddr E EA m dst S VB EB L K B embBC embAB w) (k : ℕ)
    (hk : k < m) :
    Triple w p (CEInv mem bAddr E EA m dst S VB EB L K B embBC embAB k)
      (.assign 12 (.load (.bin .add (.reg 2) (.reg 13))) ;;
        .store (.bin .add (.reg 4) (.reg 13)) (.reg 14) ;;
        .call 15 fw [.reg 0, .reg 1, .reg 12, .reg 14, .reg 5, .reg 6, .reg 7, .reg 8] ;;
        .assign 16 (.load (.reg 14)) ;;
        .assign 17 (.load (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))) ;;
        .assign 14 (.bin .add (.bin .add (.bin .add (.reg 14) (.const 2)) (.reg 16)) (.reg 17)))
      (normalPost fun st₁ =>
        CEInv mem bAddr E EA m dst S VB EB L K B embBC embAB (k + 1)
          { st₁ with regs := Function.update st₁.regs 13 (k + 1) } ∧ st₁.regs 13 = k)
      (fun _ => K * (120 * L + 620) + 280) := by
  obtain ⟨hG, hEmb, hBnd, hGS, hEA, hBA, hshape, hedg, hvw, hK, hL, hEV, hSV, hVE, hED, hdw,
    hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r13, r14, hkm, hoffs, hdone, hout⟩ := hI
  set X := 2 + 2 * (K * L) with hXdef
  set cur := dst + m + embOffs (compose B embBC embAB) k with hcur
  have hkX : k * X + X ≤ m * X := by
    have := Nat.mul_le_mul_right X (show k + 1 ≤ m by omega); rw [Nat.succ_mul] at this
    exact this
  have hEAk : EA + k < S := by have := hBA.1; omega
  set A := mem (EA + k) with hAdef
  have hAb := hBA.2 k hk
  have hst : ∀ x, x < S → st.mem x = mem x := fun x hx => hout x (Or.inl hx)
  have hneK := hK k hk
  have hneL : (embAB k).edges.length * L ≤ K * L := Nat.mul_le_mul_right _ hneK
  have hcw : cur + X < 2 ^ w := by omega
  have hEm := hBnd.1
  have hAenc := walk_encode_length (embAB k)
  have e12 : (Expr.load (.bin .add (.reg 2) (.reg 13))).eval w st = some A :=
    ev_load' (ev_add (ev_reg r2 (by omega)) (ev_reg r13 (by omega)) (by omega)) (hst _ hEAk)
  let s1 : State := { st with regs := Function.update st.regs 12 A }
  have esa : (Expr.bin .add (.reg 4) (.reg 13)).eval w s1 = some (dst + k) :=
    ev_add (ev_reg (v := dst) (by simp [s1, r4]) (by omega))
      (ev_reg (v := k) (by simp [s1, r13]) (by omega)) (by omega)
  have esv : (Expr.reg 14).eval w s1 = some cur :=
    ev_reg (v := cur) (by simp [s1, r14]) (by omega)
  let s2 : State := { s1 with mem := Function.update s1.mem (dst + k) cur }
  have hs2 : ∀ x, x ≠ dst + k → s2.mem x = st.mem x := fun x hx => by
    simp only [s2, s1]; rw [Function.update_of_ne hx]
  have hlow2 : ∀ x < S, s2.mem x = mem x := fun x hx => by
    rw [hs2 x (by omega), hst x hx]
  have hargs : evalArgs w s2 [.reg 0, .reg 1, .reg 12, .reg 14, .reg 5, .reg 6, .reg 7, .reg 8] =
      some [bAddr, E, A, cur, S, VB, EB, L] := by
    simp [evalArgs, Expr.eval, s2, s1, r0, r1, r5, r6, r7, r8, r14]
  have hGs : GraphAt s2.mem bAddr B :=
    hG.of_agree_below (by rw [graph_encode_length]; omega) hlow2
  obtain ⟨hEs, hBs⟩ := embAt_preserve hEmb hBnd hlow2
  have hWA : WalkAt s2.mem A (embAB k) := (hEA k hk).of_agree_below hAb hlow2
  have hpreW : ComposeWalkPre s2.mem bAddr E A cur S VB EB L B embBC (embAB k) w :=
    ⟨hGs, hEs, hBs, hGS, hWA, hAb, hshape k hk, hedg k hk, hvw k hk, hL, hEV, hSV,
      by omega, by omega, by omega, hw1⟩
  refine runs_start_le ?_
  refine runs_seq_assign_le e12 ?_
  refine runs_seq_store_le esa esv ?_
  refine runs_seq_call_le hfw hargs ?_ ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, hpreW⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost
  obtain ⟨hW0, hlen0, hfr0⟩ := hpost _ _ _ _ _ _ _ _ _ _ _ rfl hpreW
  have hW : WalkAt mem₁ cur (compose B embBC embAB k) := hW0
  have hlen : (Walk.encode (compose B embBC embAB k)).length ≤ X := by
    have : (Walk.encode (compose B embBC embAB k)).length ≤
        2 + 2 * ((embAB k).edges.length * L) := hlen0
    omega
  have hfr : ∀ x, x < S ∨ (EB + (embAB k).edges.length * L ≤ x ∧ x < cur) ∨
      cur + (Walk.encode (compose B embBC embAB k)).length ≤ x → mem₁ x = s2.mem x := hfr0
  obtain ⟨hnv, -, hne, -⟩ := walkAt_iff.mp hW
  have hWl := walk_encode_length (compose B embBC embAB k)
  set nv := (compose B embBC embAB k).verts.length with hnvdef
  set ne := (compose B embBC embAB k).edges.length with hnedef
  let s3 : State := { mem := mem₁, regs := Function.update s2.regs 15 v₁, pos := pos₁ }
  have e16 : (Expr.load (.reg 14)).eval w s3 = some nv :=
    ev_load' (ev_reg (v := cur) (by simp [s3, s2, s1, r14]) (by omega)) hnv
  let s4 : State := { s3 with regs := Function.update s3.regs 16 nv }
  have e17 : (Expr.load (.bin .add (.bin .add (.reg 14) (.const 1)) (.reg 16))).eval w s4 =
      some ne :=
    ev_load' (ev_add (ev_add (ev_reg (v := cur) (by simp [s4, s3, s2, s1, r14]) (by omega))
      (ev_const hw1) (by omega)) (ev_reg (v := nv) (by simp [s4]) (by omega)) (by omega)) hne
  let s5 : State := { s4 with regs := Function.update s4.regs 17 ne }
  have e14 : (Expr.bin .add (.bin .add (.bin .add (.reg 14) (.const 2)) (.reg 16)) (.reg 17)).eval
      w s5 = some (cur + 2 + nv + ne) :=
    ev_add (ev_add (ev_add (ev_reg (v := cur) (by simp [s5, s4, s3, s2, s1, r14]) (by omega))
      (ev_const (c := 2) (by omega)) (by omega)) (ev_reg (v := nv) (by simp [s5, s4]) (by omega))
      (by omega)) (ev_reg (v := ne) (by simp [s5]) (by omega)) (by omega)
  have hoffs_succ : embOffs (compose B embBC embAB) (k + 1) =
      embOffs (compose B embBC embAB) k + (2 + nv + ne) := by
    rw [embOffs, walk_encode_length]
  have hmid : ∀ x, dst ≤ x → x < cur → x ≠ dst + k → mem₁ x = st.mem x := fun x h1 h2 h3 => by
    rw [hfr x (Or.inr (Or.inl ⟨by omega, h2⟩)), hs2 x h3]
  refine runs_seq_assign_le e16 ?_
  refine runs_seq_assign_le e17 ?_
  refine runs_assign_le e14 ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, by omega, ?_, ?_,
    ?_⟩, by simp [r13]⟩ ?_
  · simp [r0]
  · simp [r1]
  · simp [r2]
  · simp [r3]
  · simp [r4]
  · simp [r5]
  · simp [r6]
  · simp [r7]
  · simp [r8]
  · simp only [Function.update_of_ne (show (14 : ℕ) ≠ 13 by omega), Function.update_self]
    rw [hoffs_succ]; omega
  · rw [hoffs_succ, ← hXdef, Nat.succ_mul]; omega
  · intro t ht
    dsimp only
    rcases Nat.lt_or_ge t k with htk | htk
    · obtain ⟨hptr, hwalk⟩ := hdone t htk
      have hmono := embOffs_mono (compose B embBC embAB) (show t + 1 ≤ k by omega)
      rw [embOffs] at hmono
      refine ⟨?_, ListAt.of_agree hwalk fun i hi => ?_⟩
      · rw [hmid _ (by omega) (by omega) (by omega)]; exact hptr
      · rw [hmid _ (by omega) (by omega) (by omega)]
    · have htk' : t = k := by omega
      rw [htk']
      refine ⟨?_, hW⟩
      rw [hfr _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
      show Function.update st.mem (dst + k) cur (dst + k) = cur
      rw [Function.update_self]
  · intro x hx
    dsimp only
    rw [hoffs_succ] at hx
    rw [hfr x (by omega), hs2 x (by omega)]
    exact hout x (by omega)
  · simp only [Expr.size, argsSize, composeWalkContract, List.getD_cons_succ,
      List.getD_cons_zero]
    obtain ⟨hnvA, -, hneA, -⟩ := walkAt_iff.mp (hEA k hk)
    have hA1 : Function.update st.mem (dst + k) cur A = (embAB k).verts.length := by
      rw [Function.update_of_ne (by omega), hst _ (by omega)]; exact hnvA
    have hA2 : Function.update st.mem (dst + k) cur (A + 1 + (embAB k).verts.length) =
        (embAB k).edges.length := by
      rw [Function.update_of_ne (by omega), hst _ (by omega)]; exact hneA
    rw [hA1, hA2]
    have := Nat.mul_le_mul_right (120 * L + 620) hneK
    omega

/-- `composeEmbBody fw` at `f` meets `composeEmbContract`, given that `fw` holds
`composeWalkBody`. The cost is `m (K (120 L + 620) + 300) + 30`. -/
theorem composeEmb_meetsContract {w : ℕ} {p : Program} {f fw : ℕ}
    (hproc : p.procs[f]? = some (composeEmbBody fw))
    (hfw : MeetsContract w p fw (composeWalkContract w)) :
    MeetsContract w p f (composeEmbContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨bAddr, E, EA, m, dst, S, VB, EB, L, K, B, embBC, embAB, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hG, hEmb, hBnd, hGS, hEA, hBA, hshape, hedg, hvw, hK, hL, hEV, hSV, hVE, hED, hdw,
    hw1⟩ := hP'
  have hmw : m < 2 ^ w := hwords m (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 13) (lo := .const 0)
    (hi := .reg 3)
    (P := fun st => st.regs 0 = bAddr ∧ st.regs 1 = E ∧ st.regs 2 = EA ∧ st.regs 3 = m ∧
      st.regs 4 = dst ∧ st.regs 5 = S ∧ st.regs 6 = VB ∧ st.regs 7 = EB ∧ st.regs 8 = L ∧
      st.regs 14 = dst + m ∧ st.mem = mem)
    (Inv := CEInv mem bAddr E EA m dst S VB EB L K B embBC embAB)
    (K * (120 * L + 620) + 280) 0 m (Nat.zero_le _) hw1 (fun _ => hmw)
    (fun st ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q14, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4], by simp [q5],
        by simp [q6], by simp [q7], by simp [q8], by simp, by simp [q14, embOffs],
        Nat.zero_le _, by simp [embOffs], fun t ht => absurd ht (Nat.not_lt_zero _),
        fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.2.2.1 hmw)
    (fun k _ hk => composeEmb_step hfw hP k hk)
  have e14 : (Expr.bin .add (.reg 4) (.reg 3)).eval w
      (startState [bAddr, E, EA, m, dst, S, VB, EB, L, K] mem pos) = some (dst + m) :=
    ev_add (ev_reg (v := dst) (by simp [startState]) (by omega))
      (ev_reg (v := m) (by simp [startState]) hmw) (by omega)
  refine runs_start_le ?_
  refine runs_seq_assign_le e14 ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdone, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega))
    (fun bA' E' EA' m' d' S' VB' EB' L' K' B' eBC eAB h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
    have hB : B = B' := graphAt_unique hG h2.1
    subst hB
    have hAB : ∀ e < m, embAB e = eAB e := fun e he => walkAt_unique (hEA e he) (h2.2.2.2.2.1 e he)
    have hR : ∀ e < m, compose B eBC eAB e = compose B embBC embAB e := fun e he => by
      simp only [compose, ← hAB e he]
      exact composeAux_congr B _ _ fun j hj =>
        (walkAt_unique (hEmb j (hedg e he j hj)) (h2.2.1 j (hedg e he j hj))).symm
    rw [embOffs_congr hR]
    refine ⟨fun e he => ?_, ⟨by omega, fun e he => ?_⟩,
      fun e he => by rw [(hdone e he).1]; omega, hout⟩
    · rw [hR e he, (hdone e he).1]; exact (hdone e he).2
    · rw [hR e he, (hdone e he).1]
      have hmono := embOffs_mono (compose B embBC embAB) (show e + 1 ≤ m by omega)
      rw [embOffs] at hmono
      omega
  · simp only [Expr.size, composeEmbContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    nlinarith [Nat.mul_le_mul_left m (show K * (120 * L + 620) + 280 + 1 + 8 ≤
      K * (120 * L + 620) + 300 by omega)]

/-! ### The shape hypotheses of `ComposeEmbPre` hold for embeddings -/

/-- A valid walk has one more vertex than edges, or is empty. -/
lemma isWalk_shape {H : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk H u v) :
    P.verts.length = P.edges.length + 1 ∨ (P.verts = [] ∧ P.edges = []) := by
  rcases hP.2.2 with ⟨h1, h2, -⟩ | ⟨-, h2, -⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl h2

/-- A valid walk with an edge has a vertex. -/
lemma isWalk_verts_ne_nil {H : Graph} {u v : ℕ} {P : Walk} (hP : P.IsWalk H u v)
    (he : P.edges ≠ []) : P.verts ≠ [] := by
  rcases isWalk_shape hP with h | ⟨-, h⟩
  · intro hv; simp [hv] at h
  · exact absurd h he

/-- Each walk of an embedding of `G` into `H` has one more vertex than edges or is empty, and
uses only edges of `H`. -/
lemma isEmbedding_walk_facts {G H : Graph} {emb : ℕ → Walk} (h : IsEmbedding G H emb) {e : ℕ}
    (he : e < G.m) :
    ((emb e).verts.length = (emb e).edges.length + 1 ∨
      ((emb e).verts = [] ∧ (emb e).edges = [])) ∧
    ((emb e).edges ≠ [] → (emb e).verts ≠ []) ∧ (∀ j ∈ (emb e).edges, j < H.m) := by
  have hW := h.2 e he
  refine ⟨isWalk_shape hW, isWalk_verts_ne_nil hW, fun j hj => ?_⟩
  rcases hW.2.2 with ⟨-, h2, -⟩ | ⟨-, -, -, -, h5, -⟩
  · simp [h2] at hj
  · exact h5 j hj

end MinCostFlow.Spanner
