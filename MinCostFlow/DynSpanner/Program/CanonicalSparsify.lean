module

public import MinCostFlow.DynSpanner.Program.SparsifyContract
public import MinCostFlow.DynSpanner.Program.GraphTranslateEmit
public import WordRAM.Link

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Canonical Guest Execution and Relocation for Static `Sparsify`

Constructs the canonical `MGraph` static sparsifier `canonicalSparsify impl` induced by any
deterministic `impl : SparsifyImpl`, proves `canonicalSparsify_spec : DynSpanner.SparsifySpec ...`,
and verifies relocated fresh-memory execution (`canonical_sparsify_relocated_run`) via
`WordRAM.Link.runs_relocStmt` with full `ZeroFrom` preservation.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.Cited

@[expose] public section

/-! ## Determinism, register-bound, and walk-congruence helpers -/

/-- A deterministic `WordRAM.Program` (`∀ s ∈ p.procs, s.NoRand`) evaluates identically under any
random tape `ω₁, ω₂` on any statement `s` with `s.NoRand`. -/
theorem exec_noRand {w : ℕ} {p : Program} (hp : p.IsDeterministic) :
    ∀ (fuel : ℕ) {ω₁ ω₂ : ℕ → Bool} {s : Stmt}, s.NoRand → ∀ {st : State},
      exec w p ω₁ fuel s st = exec w p ω₂ fuel s st
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, ω₁, ω₂, s, hs, st => by
    cases s with
    | nop => rfl
    | assign r e => rfl
    | store a e => rfl
    | rand r => simp [Stmt.NoRand] at hs
    | ret e => rfl
    | seq s₁ s₂ =>
      rcases hs with ⟨hs₁, hs₂⟩
      simp only [exec]
      rw [exec_noRand hp fuel hs₁]
      cases exec w p ω₂ fuel s₁ st with
      | none => rfl
      | some res =>
        rcases res with ⟨o, st', c⟩
        cases o with
        | normal => simp only; rw [exec_noRand hp fuel hs₂ (ω₂ := ω₂)]
        | returned v => rfl
    | cond e s₁ s₂ =>
      rcases hs with ⟨hs₁, hs₂⟩
      simp only [exec]
      cases e.eval w st with
      | none => rfl
      | some v =>
        by_cases hv : v = 0
        · simp only [hv, ↓reduceIte]; rw [exec_noRand hp fuel hs₂ (ω₂ := ω₂)]
        · simp only [hv, ↓reduceIte]; rw [exec_noRand hp fuel hs₁ (ω₂ := ω₂)]
    | loop e body =>
      simp only [Stmt.NoRand] at hs
      simp only [exec]
      cases e.eval w st with
      | none => rfl
      | some v =>
        by_cases hv : v = 0
        · simp [hv]
        · simp only [hv, ↓reduceIte]
          rw [exec_noRand hp fuel hs]
          cases exec w p ω₂ fuel body st with
          | none => rfl
          | some res =>
            rcases res with ⟨o, st', c⟩
            cases o with
            | normal =>
              simp only
              rw [exec_noRand hp fuel (by simpa [Stmt.NoRand] using hs) (ω₂ := ω₂)]
            | returned u => rfl
    | call r f args =>
      simp only [exec]
      cases evalArgs w st args with
      | none => rfl
      | some vs =>
        cases hf : p.procs[f]? with
        | none => rfl
        | some body =>
          have hbody : body.NoRand := hp body (List.mem_of_getElem? hf)
          simp only
          rw [exec_noRand hp fuel hbody]

theorem exec_pos_of_noRand {w : ℕ} {p : Program} (hp : p.IsDeterministic) :
    ∀ (fuel : ℕ) {ω : ℕ → Bool} {s : Stmt}, s.NoRand →
      ∀ {st st' : State} {o : Outcome} {c : ℕ},
        exec w p ω fuel s st = some (o, st', c) → st'.pos = st.pos
  | 0, _, _, _, _, _, _, _, h => by simp [exec] at h
  | fuel + 1, ω, s, hs, st, st', o, c, h => by
    cases s with
    | nop => simp [exec] at h; rcases h with ⟨_, rfl, _⟩; rfl
    | assign r e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => rw [he] at h; cases h
      | some v => rw [he] at h; cases h; rfl
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st with
      | none => rw [ha] at h; cases h
      | some x =>
        cases he : e.eval w st with
        | none => rw [ha, he] at h; cases h
        | some v => rw [ha, he] at h; cases h; rfl
    | rand r => simp [Stmt.NoRand] at hs
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => rw [he] at h; cases h
      | some v => rw [he] at h; cases h; rfl
    | seq s₁ s₂ =>
      rcases hs with ⟨hs₁, hs₂⟩
      simp only [exec] at h
      cases h1 : exec w p ω fuel s₁ st with
      | none => rw [h1] at h; simp at h
      | some res =>
        rw [h1] at h
        rcases res with ⟨o₁, st₁, c₁⟩
        have hp1 := exec_pos_of_noRand hp fuel hs₁ h1
        cases o₁ with
        | returned v => simp at h; rcases h with ⟨_, rfl, _⟩; exact hp1
        | normal =>
          simp only at h
          cases h2 : exec w p ω fuel s₂ st₁ with
          | none => rw [h2] at h; simp at h
          | some res₂ =>
            rw [h2] at h
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp at h; rcases h with ⟨_, rfl, _⟩
            exact (exec_pos_of_noRand hp fuel hs₂ h2).trans hp1
    | cond e s₁ s₂ =>
      rcases hs with ⟨hs₁, hs₂⟩
      simp only [exec] at h
      cases he : e.eval w st with
      | none => rw [he] at h; cases h
      | some v =>
        rw [he] at h; simp only at h
        split_ifs at h with hv
        · cases h1 : exec w p ω fuel s₂ st with
          | none => rw [h1] at h; cases h
          | some res =>
            rw [h1] at h; rcases res with ⟨o₁, st₁, c₁⟩
            cases h; exact exec_pos_of_noRand hp fuel hs₂ h1
        · cases h1 : exec w p ω fuel s₁ st with
          | none => rw [h1] at h; cases h
          | some res =>
            rw [h1] at h; rcases res with ⟨o₁, st₁, c₁⟩
            cases h; exact exec_pos_of_noRand hp fuel hs₁ h1
    | loop e body =>
      simp only [Stmt.NoRand] at hs
      simp only [exec] at h
      cases he : e.eval w st with
      | none => rw [he] at h; cases h
      | some v =>
        rw [he] at h; simp only at h
        split_ifs at h with hv
        · cases h; rfl
        · cases h1 : exec w p ω fuel body st with
          | none => rw [h1] at h; simp at h
          | some res =>
            rw [h1] at h
            rcases res with ⟨o₁, st₁, c₁⟩
            have hp1 := exec_pos_of_noRand hp fuel hs h1
            cases o₁ with
            | returned u => simp at h; rcases h with ⟨_, rfl, _⟩; exact hp1
            | normal =>
              simp only at h
              cases h2 : exec w p ω fuel (.loop e body) st₁ with
              | none => rw [h2] at h; simp at h
              | some res₂ =>
                rw [h2] at h
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp at h; rcases h with ⟨_, rfl, _⟩
                exact (exec_pos_of_noRand hp fuel (by simpa [Stmt.NoRand] using hs) h2).trans hp1
    | call r f args =>
      simp only [exec] at h
      cases ha : evalArgs w st args with
      | none => rw [ha] at h; cases h
      | some vs =>
        cases hf : p.procs[f]? with
        | none => rw [ha, hf] at h; cases h
        | some body =>
          rw [ha, hf] at h; simp only at h
          cases h1 : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
          | none => rw [h1] at h; cases h
          | some res =>
            rw [h1] at h
            rcases res with ⟨o₁, st₁, c₁⟩
            have hpos := exec_pos_of_noRand hp fuel (hp body (List.mem_of_getElem? hf)) h1
            cases h; exact hpos

theorem stmt_regBound_le_program {Q : Program} {f : ℕ} {body : Stmt}
    (hf : Q.procs[f]? = some body) : body.regBound ≤ Q.regBound := by
  have hmem : body ∈ Q.procs := List.mem_of_getElem? hf
  have hfold : ∀ (l : List Stmt), body ∈ l →
      body.regBound ≤ List.foldr (fun s acc => max s.regBound acc) 0 l := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons x xs ih =>
      rcases List.mem_cons.mp hl with rfl | hxs
      · exact Nat.le_max_left _ _
      · exact le_trans (ih hxs) (Nat.le_max_right _ _)
  exact le_trans (hfold Q.procs hmem) (by simp [Program.regBound])

private lemma walk_encode_inj {P₁ P₂ : Walk} (h : P₁.encode = P₂.encode) : P₁ = P₂ := by
  have h0 : P₁.verts.length = P₂.verts.length := by
    have := congr_arg List.head? h
    simpa [Walk.encode] using this
  have htail : P₁.verts ++ P₁.edges.length :: P₁.edges =
      P₂.verts ++ P₂.edges.length :: P₂.edges := by
    have := congr_arg List.tail h
    simpa [Walk.encode] using this
  obtain ⟨hv, hrest⟩ := List.append_inj htail h0
  have he : P₁.edges = P₂.edges := by
    have := congr_arg List.tail hrest
    simpa using this
  cases P₁; cases P₂; simp_all

private lemma walkAt_inj {mem : ℕ → ℕ} {a : ℕ} {P₁ P₂ : Walk}
    (h₁ : WalkAt mem a P₁) (h₂ : WalkAt mem a P₂) : P₁ = P₂ := by
  have henc_len : P₁.encode.length = P₂.encode.length := by
    have h1 : P₁.verts.length = P₂.verts.length := by
      have a1 : mem a = P₁.verts.length := by simpa [WalkAt, Walk.encode] using h₁ 0 (by simp [Walk.encode])
      have a2 : mem a = P₂.verts.length := by simpa [WalkAt, Walk.encode] using h₂ 0 (by simp [Walk.encode])
      exact a1.symm.trans a2
    have h2 : P₁.edges.length = P₂.edges.length := by
      have idx_lt₁ : P₁.verts.length + 1 < (P₁.verts.length :: P₁.verts ++ P₁.edges.length :: P₁.edges).length := by simp
      have idx_lt₂ : P₂.verts.length + 1 < (P₂.verts.length :: P₂.verts ++ P₂.edges.length :: P₂.edges).length := by simp
      have a1 : mem (a + (P₁.verts.length + 1)) = P₁.edges.length := by
        have hget : mem (a + (P₁.verts.length + 1)) =
            (P₁.verts.length :: P₁.verts ++ P₁.edges.length :: P₁.edges)[P₁.verts.length + 1]'idx_lt₁ :=
          h₁ (P₁.verts.length + 1) (by simp [Walk.encode])
        rw [List.getElem_append_right (by simp)] at hget
        simpa using hget
      have a2 : mem (a + (P₂.verts.length + 1)) = P₂.edges.length := by
        have hget : mem (a + (P₂.verts.length + 1)) =
            (P₂.verts.length :: P₂.verts ++ P₂.edges.length :: P₂.edges)[P₂.verts.length + 1]'idx_lt₂ :=
          h₂ (P₂.verts.length + 1) (by simp [Walk.encode])
        rw [List.getElem_append_right (by simp)] at hget
        simpa using hget
      rw [← h1] at a2
      exact a1.symm.trans a2
    simp [Walk.encode, h1, h2]
  apply walk_encode_inj
  refine List.ext_getElem henc_len fun i hi₁ hi₂ => ?_
  exact (h₁ i hi₁).symm.trans (h₂ i hi₂)

private lemma composeAux_congr (B : Cited.Graph) (f₁ f₂ : ℕ → Walk) :
    ∀ (vs cs : List ℕ), (∀ j ∈ cs, f₁ j = f₂ j) →
      Spanner.composeAux B f₁ vs cs = Spanner.composeAux B f₂ vs cs
  | u :: v :: vs, j :: js, h => by
    simp only [Spanner.composeAux]
    rw [h j List.mem_cons_self,
      composeAux_congr B f₁ f₂ (v :: vs) js fun k hk => h k (List.mem_cons_of_mem _ hk)]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _, [], _ => rfl

private lemma vcong_congr_emb {G H : Cited.Graph} {wG : ℕ → ℝ} {f₁ f₂ : ℕ → Walk}
    (hf : ∀ j < G.m, f₁ j = f₂ j) :
    Spanner.vcong G H wG f₁ = Spanner.vcong G H wG f₂ := by
  unfold Spanner.vcong Spanner.vcongAt
  congr 1; funext vH
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨hj, hmem⟩ <;> refine ⟨hj, ?_⟩
  · rwa [← hf j hj]
  · rwa [hf j hj]

private lemma length_congr_emb {G : Cited.Graph} {f₁ f₂ : ℕ → Walk}
    (hf : ∀ j < G.m, f₁ j = f₂ j) :
    Spanner.length G f₁ = Spanner.length G f₂ := by
  unfold Spanner.length
  refine Finset.fold_congr fun j hj => ?_
  rw [hf j (Finset.mem_range.mp hj)]

private lemma citedSparsifyProp_congr_emb {mMax : ℕ} {γ_c γ_ℓ K_s : ℝ} {p_s : ℕ}
    {H' J : Cited.Graph} {emb₁ emb₂ : ℕ → Walk}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (heq : ∀ j < J.m, emb₁ j = emb₂ j)
    (h : CitedSparsifyProp mMax γ_c γ_ℓ K_s p_s H' J emb₁ cJtilde kept embJJtilde) :
    CitedSparsifyProp mMax γ_c γ_ℓ K_s p_s H' J emb₂ cJtilde kept embJJtilde := by
  rcases h with ⟨hnodup, hkept, hcJn, hcJed, hcJvalid, hembJJ, hvcong, hlen, hsp⟩
  refine ⟨hnodup, hkept, hcJn, hcJed, hcJvalid, hembJJ, ?_, hlen, hsp⟩
  have hcomp_eq : ∀ j < J.m,
      Spanner.compose cJtilde (Spanner.restrictEmb emb₁ kept) embJJtilde j =
      Spanner.compose cJtilde (Spanner.restrictEmb emb₂ kept) embJJtilde j := by
    intro j hj
    unfold Spanner.compose
    refine composeAux_congr cJtilde _ _ _ _ fun c hc => ?_
    have hw := hembJJ.2 j hj
    have hc_lt : c < cJtilde.m := by
      rcases hw with ⟨_, _, ⟨_, hPe, _⟩ | ⟨_, _, _, _, hedges, _⟩⟩
      · simp [hPe] at hc
      · exact hedges c hc
    have hc_k : c < kept.length := by simpa [Cited.Graph.m, hcJed] using hc_lt
    simp only [Spanner.restrictEmb, List.getD_eq_getElem _ 0 hc_k]
    exact heq _ (hkept _ (List.getElem_mem hc_k))
  have hv1 := vcong_congr_emb (H := H') (wG := fun _ => 1) hcomp_eq
  have hv2 := vcong_congr_emb (H := H') (wG := fun _ => 1) heq
  have hl := length_congr_emb heq
  rwa [← hv1, ← hv2, ← hl]

/-! ## Word-size and guest precondition bounds for `canonSparsifyInput` -/

private lemma le_foldr_max_of_mem {a : ℕ} : ∀ {l : List ℕ}, a ∈ l → a ≤ l.foldr max 0
  | x :: xs, h => by
    rcases List.mem_cons.mp h with rfl | hxs
    · exact Nat.le_max_left _ _
    · exact le_trans (le_foldr_max_of_mem hxs) (Nat.le_max_right _ _)

theorem canonSparsifyInput_length_ge_3 (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    3 ≤ (canonSparsifyInput H' J emb).length := by
  rw [canonSparsifyInput_length]; omega

theorem citedMaxWord_initMem_eq (x : List ℕ) :
    citedMaxWord (initMem x) x.length = x.foldr max 0 := by
  unfold citedMaxWord
  have hmap : (List.range x.length).map (initMem x) = x := by
    refine List.ext_getElem (by simp) fun i hi _ => ?_
    simp only [List.getElem_map, List.getElem_range]
    unfold initMem
    exact List.getD_eq_getElem x 0 (by simpa using hi)
  rw [hmap]

theorem canonSparsifyInput_inputSize_le (H' J : MGraph) (emb : MinCostFlow.Embedding) :
    let x := canonSparsifyInput H' J emb
    citedInputSize (initMem x) ≤ 3 * (x.length + x.foldr max 0) := by
  intro x
  set cH := toCitedH H' J emb
  set cJ := toCitedJ J
  set cEmb := embToCited H' J emb
  have hx := listAt_initMem x
  obtain ⟨hm0, hm1, _, hGH, hGJ, _, _⟩ := canonSparsifyInput_decomp hx
  have hEmb := (canonSparsifyInput_EmbAt hx).1
  rw [zero_add] at hGH hGJ
  have hGH' : GraphAt (initMem x) (initMem x 0) cH := by rw [hm0]; exact hGH
  have hGJ' : GraphAt (initMem x) (initMem x 1) cJ := by rw [hm1]; exact hGJ
  rw [citedInputSize_eq hGH' hGJ' hEmb]
  have hxLen : x.length = 3 + (2 + 2 * cH.m) + (2 + 2 * cJ.m) + cJ.m +
      ((List.range cJ.m).map cEmb |>.flatMap Walk.encode).length := by
    simpa [cH, cJ, cEmb, toCitedJ_m] using canonSparsifyInput_length H' J emb
  have h3_lt : 3 < x.length := by rw [hxLen]; omega
  have hcHn_eq : x[3]'h3_lt = cH.n := by
    have h1 := hGH 0 (by simp [Cited.Graph.encode])
    have hx3 : initMem x 3 = x[3]'h3_lt := List.getD_eq_getElem x 0 h3_lt
    exact hx3.symm.trans (by simpa [Cited.Graph.encode] using h1)
  have hcHn_le : cH.n ≤ x.foldr max 0 := by
    rw [← hcHn_eq]; exact le_foldr_max_of_mem (List.getElem_mem h3_lt)
  have hpJ_lt : 3 + cH.encode.length < x.length := by
    rw [hxLen, graph_encode_length cH]; omega
  have hcJn_eq : x[3 + cH.encode.length]'hpJ_lt = cJ.n := by
    have h1 := hGJ 0 (by simp [Cited.Graph.encode])
    have hxJ : initMem x (3 + cH.encode.length) = x[3 + cH.encode.length]'hpJ_lt :=
      List.getD_eq_getElem x 0 hpJ_lt
    exact hxJ.symm.trans (by simpa [Cited.Graph.encode] using h1)
  have hcJn_le : cJ.n ≤ x.foldr max 0 := by
    rw [← hcJn_eq]; exact le_foldr_max_of_mem (List.getElem_mem hpJ_lt)
  have hcHm_le : cH.m ≤ x.length := by rw [hxLen]; omega
  have hcJm_le : cJ.m ≤ x.length := by rw [hxLen]; omega
  have hsum_le : ∑ j ∈ Finset.range cJ.m, (cEmb j).verts.length ≤ x.length := by
    have hflat_le : ∀ n : ℕ,
        ∑ j ∈ Finset.range n, (cEmb j).verts.length ≤
          ((List.range n).map cEmb |>.flatMap Walk.encode).length := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.map_singleton,
          List.flatMap_append, List.flatMap_singleton, List.length_append]
        have hwe : (cEmb k).verts.length ≤ (cEmb k).encode.length := by
          simp [Walk.encode]; omega
        omega
    have h1 := hflat_le cJ.m
    have h2 : ((List.range cJ.m).map cEmb |>.flatMap Walk.encode).length ≤ x.length := by
      rw [hxLen]; omega
    exact le_trans h1 h2
  dsimp only [cH, cJ, cEmb] at hcHn_le hcHm_le hcJn_le hcJm_le hsum_le ⊢
  omega

/-- For any valid `(H', J, embJH)` meeting `mMax` and non-triviality of nonempty embeddings,
`canonSparsifyInput H' J embJH` automatically satisfies `sparsifyGuestContract.pre` at guest
word size `wordSize impl.cw (canonSparsifyInput H' J embJH)`. -/
theorem canonSparsifyInput_guestPre (impl : SparsifyImpl) (mMax : ℕ)
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J) (hembJH : embJH.IsEmbedding J H') :
    let x := canonSparsifyInput H' J embJH
    let w' := wordSize impl.cw x
    (∀ a ∈ [0, x.length], a < 2 ^ w') ∧
    (sparsifyGuestContractWithTime mMax (impl.γ_c mMax) (impl.γ_ℓ mMax) impl.K_s impl.p_s
      impl.K_t (impl.γ_t mMax) impl.p_t impl.cw impl.space w').pre [0, x.length] (initMem x) := by
  intro x w'
  have hx := listAt_initMem x
  have h3 : 3 ≤ x.length := canonSparsifyInput_length_ge_3 H' J embJH
  have hcw1 : 1 ≤ impl.cw := by have := impl.hcw; omega
  have hpow := pow_lt_two_pow_wordSize hcw1 x
  have hx_ltw : x.length < 2 ^ w' := by
    have h1 : x.length < (x.length + x.foldr max 0 + 2) ^ impl.cw := by
      have hb : x.length < x.length + x.foldr max 0 + 2 := by omega
      have hp : x.length + x.foldr max 0 + 2 ≤ (x.length + x.foldr max 0 + 2) ^ impl.cw := by
        simpa using Nat.pow_le_pow_right (by omega) hcw1
      omega
    exact lt_trans h1 hpow
  have hargs_w : ∀ a ∈ [0, x.length], a < 2 ^ w' := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact Nat.zero_lt_of_lt hx_ltw
    · exact hx_ltw
  refine ⟨hargs_w, ?_⟩
  have hsz_le := canonSparsifyInput_inputSize_le H' J embJH
  have hsp_lt : x.length + impl.space (citedInputSize (initMem x)) < 2 ^ w' := by
    have h1 := impl.hcw_space x.length (x.foldr max 0) (citedInputSize (initMem x)) h3 hsz_le
    exact lt_trans h1 hpow
  have h16 : 16 ≤ 2 ^ w' := by
    have hm5 : 5 ≤ x.length + x.foldr max 0 + 2 := by omega
    have hlog2 : 2 ≤ Nat.log 2 (x.length + x.foldr max 0 + 2) := by
      have : Nat.log 2 4 ≤ Nat.log 2 (x.length + x.foldr max 0 + 2) :=
        Nat.log_mono_right (by omega)
      have h2_4 : Nat.log 2 4 = 2 := by decide
      omega
    have hw6 : 6 ≤ w' := by
      change 6 ≤ impl.cw * (Nat.log 2 (x.length + x.foldr max 0 + 2) + 1)
      have := impl.hcw
      nlinarith
    have h64 : 64 ≤ 2 ^ w' := by
      calc 64 = 2 ^ 6 := by decide
        _ ≤ 2 ^ w' := Nat.pow_le_pow_right (by omega) hw6
    omega
  obtain ⟨hm0, hm1, hm2, hGH, hGJ, _, _⟩ := canonSparsifyInput_decomp hx
  obtain ⟨hEmb, hEmbB⟩ := canonSparsifyInput_EmbAt hx
  simp only [zero_add] at hm1 hm2 hGH hGJ
  set cH := toCitedH H' J embJH
  set cJ := toCitedJ J
  set cEmb := embToCited H' J embJH
  have hxLen : x.length = 3 + (2 + 2 * cH.m) + (2 + 2 * cJ.m) + cJ.m +
      ((List.range cJ.m).map cEmb |>.flatMap Walk.encode).length := by
    simpa [cH, cJ, cEmb, toCitedJ_m] using canonSparsifyInput_length H' J embJH
  have hcJm_le : cJ.m ≤ mMax := by
    dsimp [cJ]; rw [toCitedJ_m]; exact hJm
  have hlen_cit : 1 ≤ cJ.m → 1 ≤ Spanner.length cJ cEmb := by
    intro hm
    have hEne : J.E.Nonempty := Finset.card_pos.mp (by
      rw [show cJ.m = J.m from toCitedJ_m J] at hm
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one hm)
    have h1 := hLen hEne
    simpa [cJ, cEmb, length_embToCited_eq] using h1
  refine ⟨⟨x.length, cH, cJ, cEmb, rfl, h16, h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    zeroFrom_initMem x, hsp_lt⟩
  · rw [hm0, hxLen, graph_encode_length cH]; omega
  · rw [hm1, hxLen, graph_encode_length cH, graph_encode_length cJ]; omega
  · rw [hm2, hxLen, graph_encode_length cH, graph_encode_length cJ]; omega
  · rw [hm0]; exact hGH
  · rw [hm1]; exact hGJ
  · rw [hm2]; exact hEmb
  · rw [hm2]; exact hEmbB
  · exact toCitedH_isValid hH' hJ hembJH
  · exact toCitedJ_isValid hJ
  · exact embToCited_isEmbedding hJ hembJH
  · exact hcJm_le
  · exact hlen_cit
  · rw [citedMaxWord_initMem_eq x]
    exact le_rfl

/-! ## Canonical `Sparsify` extraction and `DynSpanner.SparsifySpec` -/

/-- Canonical guest Word-RAM witness exists whenever `(H', J, embJH)` meets edge cap `mMax`. -/
theorem canonicalGuestRun_exists (impl : SparsifyImpl) (mMax : ℕ)
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hH' : H'.IsValid) (hJ : J.IsValid) (hJm : J.m ≤ mMax)
    (hLen : J.E.Nonempty → 1 ≤ embJH.length J) (hembJH : embJH.IsEmbedding J H') :
    let x := canonSparsifyInput H' J embJH
    let w' := wordSize impl.cw x
    ∃ (body : Stmt) (o : Outcome) (st' : State) (cost : ℕ)
      (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk),
      impl.program.procs[0]? = some body ∧
      Runs w' impl.program (fun _ => false) body
        (startState [0, x.length] (initMem x) 0) o st' cost ∧
      x.length ≤ o.value ∧
      o.value < 2 ^ w' ∧
      ZeroFrom st'.mem o.value ∧
      CitedSparsifyProp mMax (impl.γ_c mMax) (impl.γ_ℓ mMax) impl.K_s impl.p_s
        (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) cJtilde kept embJJtilde ∧
      SparsifyOutRelocAt st'.mem 0 x.length o.value (toCitedJ J).m cJtilde kept embJJtilde ∧
      cost ≤ ⌈impl.K_t * (impl.γ_t mMax) *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ := by
  intro x w'
  obtain ⟨hargs_w, hpre⟩ := canonSparsifyInput_guestPre impl mMax hH' hJ hJm hLen hembJH
  have hEnds := impl.spec mMax w' [0, x.length] (initMem x) 0 (fun _ => false) hargs_w hpre
  rcases hEnds with ⟨body, hbody, o, st', cost, hrun, hpost, hcost⟩
  rcases hpost with ⟨⟨hret_ge, hret_le, _, hz, _⟩,
    heap, cH, cJ, cEmb, cJtilde, kept, embJJtilde, hargs_eq, hGH, hGJ, hEmb, hProp, hOut⟩
  simp only [List.cons.injEq, true_and, and_true] at hargs_eq
  rcases hargs_eq with ⟨rfl, rfl⟩
  have hx := listAt_initMem x
  obtain ⟨hm0, hm1, hm2, hGH₀, hGJ₀, _, _⟩ := canonSparsifyInput_decomp hx
  obtain ⟨hEmb₀, _⟩ := canonSparsifyInput_EmbAt hx
  rw [zero_add] at hGH₀ hGJ₀
  have hcH_eq : cH = toCitedH H' J embJH := by
    rw [hm0] at hGH
    exact (graphAt_iff_readGraph.mp hGH).symm.trans (graphAt_iff_readGraph.mp hGH₀)
  have hcJ_eq : cJ = toCitedJ J := by
    rw [hm1] at hGJ
    exact (graphAt_iff_readGraph.mp hGJ).symm.trans (graphAt_iff_readGraph.mp hGJ₀)
  have hcEmb_eq : ∀ j < (toCitedJ J).m, cEmb j = embToCited H' J embJH j := by
    intro j hj
    have hw1 : WalkAt (initMem x) (initMem x (initMem x 2 + j)) (cEmb j) := by
      rw [← hcJ_eq] at hj; exact hEmb j hj
    have hw2 : WalkAt (initMem x) (initMem x (initMem x 2 + j)) (embToCited H' J embJH j) := by
      rw [hm2]; exact hEmb₀ j hj
    exact walkAt_inj hw1 hw2
  subst hcH_eq hcJ_eq
  have hProp' := citedSparsifyProp_congr_emb hcEmb_eq hProp
  have hsp_lt : o.value < 2 ^ w' := by
    simp only [heapArg] at hret_le hpre
    exact lt_of_le_of_lt hret_le hpre.2.2
  have hcost' : cost ≤ ⌈impl.K_t * (impl.γ_t mMax) *
      (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ := by
    have hrJ : readGraph (initMem x) (initMem x 1) = toCitedJ J := by
      rw [hm1]; exact graphAt_iff_readGraph.mp hGJ₀
    have hrEmb : readCitedEmbLen (initMem x) (initMem x 2) (toCitedJ J).m =
        Spanner.length (toCitedJ J) (embToCited H' J embJH) := by
      rw [hm2]
      exact readCitedEmbLen_eq_length hEmb₀ (embToCited_isEmbedding hJ hembJH)
    have hJn : (toCitedJ J).n = J.n := by dsimp [toCitedJ]; exact vertsOf_length J.V
    have hJm' : (toCitedJ J).m = J.m := toCitedJ_m J
    have hl : readCitedEmbLen (initMem x) (initMem x 2) (toCitedJ J).m = embJH.length J := by
      rw [hrEmb, length_embToCited_eq]
    dsimp only [sparsifyGuestContractWithTime, WordRAM.heapContract] at hcost
    rw [hrJ, hl, hJn, hJm'] at hcost
    exact hcost
  exact ⟨body, o, st', cost, cJtilde, kept, embJJtilde, hbody, hrun,
    by simpa [heapArg] using hret_ge, hsp_lt, hz, hProp', hOut, hcost'⟩

/-- Any two deterministic guest runs from `canonicalGuestRun_exists` on the same `(H', J, embJH)`
(at possibly different edge caps `mMax₁, mMax₂`) yield the identical decoded output `(cJtilde, kept,
embJJtilde)` (on `j < (toCitedJ J).m`) and `cost`. -/
private lemma canonicalGuestRun_agree {impl : SparsifyImpl} {H' J : MGraph}
    {embJH : MinCostFlow.Embedding}
    {body₁ body₂ : Stmt} {o₁ o₂ : Outcome} {st₁ st₂ : State} {cost₁ cost₂ : ℕ}
    {cJ₁ cJ₂ : Cited.Graph} {kept₁ kept₂ : List ℕ} {emb₁ emb₂ : ℕ → Walk}
    (hp₁ : impl.program.procs[0]? = some body₁)
    (hp₂ : impl.program.procs[0]? = some body₂)
    (hr₁ : Runs (wordSize impl.cw (canonSparsifyInput H' J embJH)) impl.program (fun _ => false)
      body₁ (startState [0, (canonSparsifyInput H' J embJH).length]
        (initMem (canonSparsifyInput H' J embJH)) 0) o₁ st₁ cost₁)
    (hr₂ : Runs (wordSize impl.cw (canonSparsifyInput H' J embJH)) impl.program (fun _ => false)
      body₂ (startState [0, (canonSparsifyInput H' J embJH).length]
        (initMem (canonSparsifyInput H' J embJH)) 0) o₂ st₂ cost₂)
    (ho₁ : SparsifyOutRelocAt st₁.mem 0 (canonSparsifyInput H' J embJH).length o₁.value
      (toCitedJ J).m cJ₁ kept₁ emb₁)
    (ho₂ : SparsifyOutRelocAt st₂.mem 0 (canonSparsifyInput H' J embJH).length o₂.value
      (toCitedJ J).m cJ₂ kept₂ emb₂) :
    o₁ = o₂ ∧ st₁ = st₂ ∧ cost₁ = cost₂ ∧ cJ₁ = cJ₂ ∧ kept₁ = kept₂ ∧
      ∀ j < (toCitedJ J).m, emb₁ j = emb₂ j := by
  have hbody : body₁ = body₂ := Option.some.inj (hp₁.symm.trans hp₂)
  subst hbody
  obtain ⟨rfl, rfl, rfl⟩ := Runs.det hr₁ hr₂
  rcases ho₁ with ⟨_, _, _, _, hG₁, hK₁, hW₁⟩
  rcases ho₂ with ⟨_, _, _, _, hG₂, hK₂, hW₂⟩
  simp only [zero_add] at hG₁ hK₁ hW₁ hG₂ hK₂ hW₂
  have hcJ : cJ₁ = cJ₂ :=
    (graphAt_iff_readGraph.mp hG₁).symm.trans (graphAt_iff_readGraph.mp hG₂)
  have hlenK : kept₁.length = kept₂.length := by
    have ha := hK₁ 0 (by simp)
    have hb := hK₂ 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at ha hb
    omega
  have hkept : kept₁ = kept₂ := by
    have hcons : kept₁.length :: kept₁ = kept₂.length :: kept₂ :=
      ListAt.ext hK₁ hK₂ (by simp [hlenK])
    exact (List.cons.inj hcons).2
  have hemb : ∀ j < (toCitedJ J).m, emb₁ j = emb₂ j := fun j hj =>
    walkAt_inj (hW₁ j hj).2 (hW₂ j hj).2
  exact ⟨rfl, rfl, rfl, hcJ, hkept, hemb⟩

private lemma citedEmbToMGraph_congr_emb {J : MGraph} {cJ : Cited.Graph} {kept : List ℕ}
    {emb₁ emb₂ : ℕ → Walk} (h : ∀ j < (toCitedJ J).m, emb₁ j = emb₂ j) :
    citedEmbToMGraph J cJ kept emb₁ = citedEmbToMGraph J cJ kept emb₂ := by
  funext e
  dsimp only [citedEmbToMGraph]
  split_ifs with he
  · have hidx : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
      rw [toCitedJ_m]; exact idxOf_lt_card he
    rw [h _ hidx]
  · rfl

/-- Canonical `SparsifyParams` matching `canonicalSparsify impl` at edge cap `mMax`. -/
noncomputable def canonicalSparsifyParams (impl : SparsifyImpl) (mMax : ℕ) :
    DynSpanner.SparsifyParams where
  γ_c := impl.γ_c mMax + 1
  γ_ℓ := impl.γ_ℓ mMax
  K_s := impl.K_s
  p_s := impl.p_s
  K_t := 2 * impl.K_t + 1
  γ_t := impl.γ_t mMax
  p_t := impl.p_t
  hγ_c := by linarith [impl.hγ_c mMax]
  hγ_ℓ := impl.hγ_ℓ mMax
  hK_s := impl.hK_s
  hK_t := by linarith [impl.hK_t]
  hγ_t := impl.hγ_t mMax

/-- Precondition under which `canonicalSparsify impl` extracts the deterministic guest run. -/
def CanonicalSparsifyValid (_impl : SparsifyImpl) (H' J : MGraph)
    (embJH : MinCostFlow.Embedding) : Prop :=
  1 ≤ J.n ∧ H'.IsValid ∧ J.IsValid ∧
    (J.E.Nonempty → 1 ≤ embJH.length J) ∧ embJH.IsEmbedding J H'

theorem canonicalGuestOut_exists (impl : SparsifyImpl)
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hV : CanonicalSparsifyValid impl H' J embJH) :
    ∃ (out : DynSpanner.SparsifyOut),
      ∀ {body : Stmt} {o : Outcome} {st' : State} {cost : ℕ}
        {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk},
        impl.program.procs[0]? = some body →
        Runs (wordSize impl.cw (canonSparsifyInput H' J embJH)) impl.program (fun _ => false)
          body (startState [0, (canonSparsifyInput H' J embJH).length]
            (initMem (canonSparsifyInput H' J embJH)) 0) o st' cost →
        SparsifyOutRelocAt st'.mem 0 (canonSparsifyInput H' J embJH).length o.value
          (toCitedJ J).m cJtilde kept embJJtilde →
        out = { Jtilde := outJtilde J kept
                emb := citedEmbToMGraph J cJtilde kept embJJtilde
                cost := cost } := by
  obtain ⟨body₀, o₀, st₀', cost₀, cJ₀, kept₀, emb₀, hp₀, hr₀, _, _, _, _, hOut₀, _⟩ :=
    canonicalGuestRun_exists impl J.m hV.2.1 hV.2.2.1 (le_refl _) hV.2.2.2.1 hV.2.2.2.2
  refine ⟨{ Jtilde := outJtilde J kept₀, emb := citedEmbToMGraph J cJ₀ kept₀ emb₀, cost := cost₀ },
    fun hp hr hOut => ?_⟩
  obtain ⟨_, _, hcost_eq, hcJ_eq, hkept_eq, hemb_eq⟩ :=
    canonicalGuestRun_agree hp₀ hp hr₀ hr hOut₀ hOut
  simp only [DynSpanner.SparsifyOut.mk.injEq]
  exact ⟨by rw [hkept_eq], by rw [hcJ_eq, hkept_eq]; exact citedEmbToMGraph_congr_emb hemb_eq,
    hcost_eq⟩

open Classical in
/-- Canonical `MGraph` static sparsifier induced by a deterministic fixed `impl : SparsifyImpl`
(independent of `mMax`). -/
noncomputable def canonicalSparsify (impl : SparsifyImpl)
    (H' J : MGraph) (embJH : MinCostFlow.Embedding) : DynSpanner.SparsifyOut :=
  if h : CanonicalSparsifyValid impl H' J embJH then
    Classical.choose (canonicalGuestOut_exists impl h)
  else
    { Jtilde := emptyGraphOn J
      emb := idEmb
      cost := 0 }

/-- Any guest run on valid inputs reproduces `canonicalSparsify impl H' J embJH` regardless of the
edge cap `mMax` used when witnessing `canonicalGuestRun_exists`. -/
theorem canonicalSparsify_eq_of_run {impl : SparsifyImpl} {H' J : MGraph}
    {embJH : MinCostFlow.Embedding} (hV : CanonicalSparsifyValid impl H' J embJH)
    {body : Stmt} {o : Outcome} {st' : State} {cost : ℕ}
    {cJtilde : Cited.Graph} {kept : List ℕ} {embJJtilde : ℕ → Walk}
    (hp : impl.program.procs[0]? = some body)
    (hr : Runs (wordSize impl.cw (canonSparsifyInput H' J embJH)) impl.program (fun _ => false)
      body (startState [0, (canonSparsifyInput H' J embJH).length]
        (initMem (canonSparsifyInput H' J embJH)) 0) o st' cost)
    (hOut : SparsifyOutRelocAt st'.mem 0 (canonSparsifyInput H' J embJH).length o.value
      (toCitedJ J).m cJtilde kept embJJtilde) :
    canonicalSparsify impl H' J embJH =
      { Jtilde := outJtilde J kept
        emb := citedEmbToMGraph J cJtilde kept embJJtilde
        cost := cost } := by
  classical
  simp only [canonicalSparsify, dite_eq_left_of_eq_true (eq_true hV)]
  exact Classical.choose_spec (canonicalGuestOut_exists impl hV) hp hr hOut

/-- The fixed canonical sparsifier `canonicalSparsify impl` satisfies
`DynSpanner.SparsifySpecWithTime` at **every** edge cap `mMax`. -/
theorem canonicalSparsify_spec_with_time (impl : SparsifyImpl) (mMax : ℕ) :
    DynSpanner.SparsifySpecWithTime mMax (canonicalSparsifyParams impl mMax)
      (canonicalSparsify impl) := by
  intro H' J embJH hH' hJ hJm hLen hembJH
  by_cases hJn : 1 ≤ J.n
  · have hV : CanonicalSparsifyValid impl H' J embJH :=
      ⟨hJn, hH', hJ, hLen, hembJH⟩
    obtain ⟨body, o, st', cost, cJtilde, kept, embJJtilde,
      hp, hr, _, _, _, hProp₂, hOut, hCost_le⟩ :=
      canonicalGuestRun_exists impl mMax hH' hJ hJm hLen hembJH
    have hOutEq := canonicalSparsify_eq_of_run hV hp hr hOut
    rw [hOutEq]
    have hMg := mGraph_props_of_citedSparsifyProp (le_trans zero_le_one (impl.hγ_c mMax))
      hH' hJ hJm hLen hembJH hProp₂
    refine ⟨hMg.1, hMg.2.1, hMg.2.2.1, hMg.2.2.2.1, hMg.2.2.2.2, ?_⟩
    have hJn1 : (1 : ℝ) ≤ (J.n : ℝ) := by exact_mod_cast hJn
    have hnm1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by
      linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m]
    have hlog_ge : 1 ≤ (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t :=
      one_le_pow₀ (by linarith [Real.log_nonneg hnm1])
    have hfac_ge : (1 : ℝ) ≤ ((J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t := by
      have hfst : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ) := by
        have hnn : 0 ≤ (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ) := by positivity
        linarith
      nlinarith
    have hgt_fac : (1 : ℝ) ≤ impl.γ_t mMax *
        (((J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t) := by
      nlinarith [impl.hγ_t mMax]
    have hceil : (cost : ℝ) ≤ impl.K_t * (impl.γ_t mMax) *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t + 1 := by
      have h1 : (cost : ℝ) ≤ ((⌈impl.K_t * (impl.γ_t mMax) *
          (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ : ℕ) : ℝ) :=
        Nat.cast_le.mpr hCost_le
      have hnn : 0 ≤ impl.K_t * (impl.γ_t mMax) *
          (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t := by
        have := impl.hK_t
        have := impl.hγ_t mMax
        positivity
      exact le_trans h1 (Nat.ceil_lt_add_one hnn).le
    have h1plus : 1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ) ≤
        2 * ((J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) := by
      have hnn : 0 ≤ (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ) := by positivity
      linarith
    have hK_nn : 0 ≤ impl.K_t * impl.γ_t mMax :=
      mul_nonneg impl.hK_t (le_trans zero_le_one (impl.hγ_t mMax))
    have hmul : impl.K_t * (impl.γ_t mMax) *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t ≤
        2 * impl.K_t * (impl.γ_t mMax) *
          ((J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
          (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t := by
      have h' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1plus hK_nn)
        (le_trans zero_le_one hlog_ge)
      linarith
    change (cost : ℝ) ≤ (2 * impl.K_t + 1) * (impl.γ_t mMax) *
        ((J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t
    nlinarith
  · have hV : ¬ CanonicalSparsifyValid impl H' J embJH := fun h => hJn h.1
    have hJn0 : J.n = 0 := by omega
    have hJV0 : J.V = ∅ := Finset.card_eq_zero.mp (by simpa [MGraph.n] using hJn0)
    have hJE0 : J.E = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have ht := (hJ e he).1
      simp [hJV0] at ht
    have hJm0 : J.m = 0 := by simp [MGraph.m, hJE0]
    have hOutEq : canonicalSparsify impl H' J embJH = ⟨emptyGraphOn J, idEmb, 0⟩ := by
      simp [canonicalSparsify, hV]
    rw [hOutEq]
    have hsub : J.IsSubgraph (emptyGraphOn J) := by
      refine ⟨Finset.Subset.rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      simp [emptyGraphOn, hJE0]
    have hemb_id : idEmb.IsEmbedding J (emptyGraphOn J) := by
      refine ⟨Finset.Subset.rfl, fun e he => ?_⟩
      simp [hJE0] at he
    have hvc0 : (embJH.comp idEmb).vcong J H' (fun _ => 1) = 0 := by
      unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
      split_ifs with hne
      · apply le_antisymm
        · refine Finset.sup'_le _ _ fun v _ => by simp [hJE0]
        · obtain ⟨v, hv⟩ := hne
          exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
            (Finset.le_sup' (fun vH =>
              ∑ e ∈ J.E with vH ∈ H'.walkVertices (J.tail e) (embJH.comp idEmb e), (1 : ℝ)) hv)
      · rfl
    have hlen0 : (embJH.comp idEmb).length J = 0 := by
      unfold MinCostFlow.Embedding.length
      simp [hJE0]
    refine ⟨hsub, hemb_id, ?_, ?_, ?_, ?_⟩
    · dsimp only [canonicalSparsifyParams]
      rw [hvc0]
      have hnn : 0 ≤ embJH.vcong J H' (fun _ => 1) := by
        unfold MinCostFlow.Embedding.vcong MinCostFlow.Embedding.vcongAt
        split_ifs with hne
        · obtain ⟨v, hv⟩ := hne
          exact le_trans (Finset.sum_nonneg fun _ _ => zero_le_one)
            (Finset.le_sup' (fun vH =>
              ∑ e ∈ J.E with vH ∈ H'.walkVertices (J.tail e) (embJH e), (1 : ℝ)) hv)
        · exact le_rfl
      have := impl.hγ_c mMax
      positivity
    · dsimp only [canonicalSparsifyParams]
      rw [hlen0]
      simp only [CharP.cast_eq_zero]
      exact mul_nonneg (by linarith [impl.hγ_ℓ mMax]) (Nat.cast_nonneg _)
    · dsimp only [canonicalSparsifyParams]
      have hm0 : (emptyGraphOn J).m = 0 := by simp [MGraph.m, emptyGraphOn]
      rw [hm0]; simp only [CharP.cast_eq_zero]
      have hnm1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by linarith
      have h1 := pow_nonneg (by linarith [Real.log_nonneg hnm1] : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) impl.p_s
      exact mul_nonneg (mul_nonneg (mul_nonneg impl.hK_s (Nat.cast_nonneg _)) (by linarith [impl.hγ_ℓ mMax])) h1
    · dsimp only [canonicalSparsifyParams]
      simp only [CharP.cast_eq_zero]
      have hnm1 : (1 : ℝ) ≤ (J.n : ℝ) + (J.m : ℝ) + 2 := by linarith
      have h1 := pow_nonneg (by linarith [Real.log_nonneg hnm1] : 0 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) impl.p_t
      have h2 : 0 ≤ (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ) := by
        have := impl.hγ_ℓ mMax; positivity
      have hgt0 : 0 ≤ impl.γ_t mMax := le_trans zero_le_one (impl.hγ_t mMax)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith [impl.hK_t]) hgt0) h2) h1

/-- Absorbing `γ_t` into `K_t` yields `DynSpanner.SparsifySpec` unconditionally at any `mMax`. -/
theorem canonicalSparsify_spec_absorb (impl : SparsifyImpl) (mMax : ℕ) :
    DynSpanner.SparsifySpec mMax (canonicalSparsifyParams impl mMax).absorbTime
      (canonicalSparsify impl) :=
  DynSpanner.sparsifySpecWithTime_iff_absorb.mp (canonicalSparsify_spec_with_time impl mMax)

/-- Unit-time-factor specialization (`γ_t mMax = 1`) recovering `DynSpanner.SparsifySpec`
directly with `canonicalSparsifyParams impl mMax`. -/
theorem canonicalSparsify_spec (impl : SparsifyImpl) (mMax : ℕ) (hγ_t : impl.γ_t mMax = 1) :
    DynSpanner.SparsifySpec mMax (canonicalSparsifyParams impl mMax)
      (canonicalSparsify impl) :=
  (DynSpanner.sparsifySpecWithTime_iff_of_one (by simpa [canonicalSparsifyParams] using hγ_t)).mp
    (canonicalSparsify_spec_with_time impl mMax)

/-! ## Relocated fresh-memory execution (`Link.runs_relocStmt`) -/

private lemma sparsifyOutRelocAt_of_reloc {w' guestBase outPtr retHeap mJ : ℕ}
    {mem_H mem_Q : ℕ → ℕ} {cJtilde : Cited.Graph} {kept : List ℕ} {emb : ℕ → Walk}
    (hret : retHeap ≤ 2 ^ w')
    (hmem : ∀ a < 2 ^ w', mem_H (guestBase + a) = mem_Q a)
    (hOut : SparsifyOutRelocAt mem_Q 0 outPtr retHeap mJ cJtilde kept emb) :
    SparsifyOutRelocAt mem_H guestBase outPtr retHeap mJ cJtilde kept emb := by
  simp only [SparsifyOutRelocAt, zero_add] at hOut
  rcases hOut with ⟨ho3, hpJ, hpK, hpE, hGJ, hLK, hWalks⟩
  have h1 : mem_H (guestBase + outPtr) = mem_Q outPtr := hmem _ (by omega)
  have h2 : mem_H (guestBase + outPtr + 1) = mem_Q (outPtr + 1) := by
    simpa [Nat.add_assoc] using hmem (outPtr + 1) (by omega)
  have h3 : mem_H (guestBase + outPtr + 2) = mem_Q (outPtr + 2) := by
    simpa [Nat.add_assoc] using hmem (outPtr + 2) (by omega)
  dsimp only [SparsifyOutRelocAt]
  rw [h1, h2, h3]
  refine ⟨ho3, hpJ, hpK, hpE, ?_, ?_, fun j hj => ?_⟩
  · intro i hi
    simpa [Nat.add_assoc] using (hmem _ (by omega)).trans (hGJ i hi)
  · intro i hi
    simp only [List.length_cons] at hi
    simpa [Nat.add_assoc] using (hmem _ (by omega)).trans (hLK i (by simpa using hi))
  · have hm_j : mem_H (guestBase + mem_Q (outPtr + 2) + j) = mem_Q (mem_Q (outPtr + 2) + j) := by
      simpa [Nat.add_assoc] using hmem (mem_Q (outPtr + 2) + j) (by omega)
    rw [hm_j]
    rcases hWalks j hj with ⟨hwj1, hwj2⟩
    refine ⟨hwj1, fun i hi => ?_⟩
    simpa [Nat.add_assoc] using (hmem _ (by omega)).trans (hwj2 i hi)

/-- Relocated execution of the deterministic guest `Sparsify` program `impl.program` inside a
host program `p` (embedded via `relocStmt impl.program.regBound b`) at `guestBase = h + 1`:
produces the EXACT output `(cJtilde, kept, embJJtilde)` and `canonicalSparsify` result for any
edge cap `mMax ≥ J.m`, preserves all memory outside `[guestBase, guestBase + 2 ^ w')`, and
maintains `ZeroFrom mem' (guestBase + retHeap)`. -/
theorem canonical_sparsify_relocated_run (impl : SparsifyImpl) (mMax : ℕ)
    {w b guestBase : ℕ} {p : Program} {ω : ℕ → Bool} {st_H : State}
    {H' J : MGraph} {embJH : MinCostFlow.Embedding}
    (hV : CanonicalSparsifyValid impl H' J embJH) (hJm : J.m ≤ mMax)
    (hpReloc : ∀ (f : ℕ) (body : Stmt), impl.program.procs[f]? = some body →
      p.procs[b + 1 + f]? = some (relocStmt impl.program.regBound b body))
    (hw' : wordSize impl.cw (canonSparsifyInput H' J embJH) ≤ w)
    (hgB1 : 1 ≤ guestBase)
    (hgBw : guestBase + 2 ^ wordSize impl.cw (canonSparsifyInput H' J embJH) ≤ 2 ^ w)
    (hw4 : 4 ≤ 2 ^ w)
    (hreg_base : st_H.regs impl.program.regBound = guestBase)
    (hreg_W : st_H.regs (impl.program.regBound + 1) =
      2 ^ wordSize impl.cw (canonSparsifyInput H' J embJH))
    (hregs_arg : ∀ r < impl.program.regBound,
      st_H.regs r = (startState [0, (canonSparsifyInput H' J embJH).length]
        (initMem (canonSparsifyInput H' J embJH)) 0).regs r)
    (hmem_in : ListAt st_H.mem guestBase (canonSparsifyInput H' J embJH))
    (hmem_zero : ZeroFrom st_H.mem (guestBase + (canonSparsifyInput H' J embJH).length)) :
    let x := canonSparsifyInput H' J embJH
    let w' := wordSize impl.cw x
    let Q := impl.program
    ∃ (body : Stmt) (o : Outcome) (st_H' : State) (c_H : ℕ)
      (cJtilde : Cited.Graph) (kept : List ℕ) (embJJtilde : ℕ → Walk) (c_Q : ℕ),
      Q.procs[0]? = some body ∧
      p.procs[b + 1]? = some (relocStmt Q.regBound b body) ∧
      Runs w p ω (relocStmt Q.regBound b body) st_H o st_H' c_H ∧
      c_H ≤ (Q.regBound + 6) * c_Q ∧
      c_Q ≤ ⌈impl.K_t * (impl.γ_t mMax) *
        (1 + (J.n : ℝ) + (J.m : ℝ) * (impl.γ_ℓ mMax) ^ 2 * (embJH.length J : ℝ)) *
        (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ impl.p_t⌉₊ ∧
      x.length ≤ o.value ∧
      o.value < 2 ^ w' ∧
      ZeroFrom st_H'.mem (guestBase + o.value) ∧
      CitedSparsifyProp mMax (impl.γ_c mMax) (impl.γ_ℓ mMax) impl.K_s impl.p_s
        (toCitedH H' J embJH) (toCitedJ J) (embToCited H' J embJH) cJtilde kept embJJtilde ∧
      SparsifyOutRelocAt st_H'.mem guestBase x.length o.value (toCitedJ J).m cJtilde kept embJJtilde ∧
      outJtilde J kept = (canonicalSparsify impl H' J embJH).Jtilde ∧
      citedEmbToMGraph J cJtilde kept embJJtilde = (canonicalSparsify impl H' J embJH).emb ∧
      c_Q = (canonicalSparsify impl H' J embJH).cost ∧
      (∀ addr, addr < guestBase ∨ guestBase + 2 ^ w' ≤ addr → st_H'.mem addr = st_H.mem addr) ∧
      st_H'.pos = st_H.pos := by
  intro x w' Q
  obtain ⟨hJn, hH', hJ, hLen, hembJH⟩ := hV
  have hV' : CanonicalSparsifyValid impl H' J embJH := ⟨hJn, hH', hJ, hLen, hembJH⟩
  obtain ⟨body, o, st_Q', c_Q, cJtilde, kept, embJJtilde,
    hQ0, hRunQ, hx_le, ho_lt, hzQ, hProp, hOutQ, hCostQ⟩ :=
    canonicalGuestRun_exists impl mMax hH' hJ hJm hLen hembJH
  have hCS := canonicalSparsify_eq_of_run hV' hQ0 hRunQ hOutQ
  obtain ⟨fuel, hexecQ⟩ := hRunQ
  have hDet : Q.IsDeterministic := impl.program_isDeterministic
  have hbody_noRand : body.NoRand := hDet body (List.mem_of_getElem? hQ0)
  have hexec_sub : exec w' Q (subBits w w' st_H.pos ω) fuel body
      (startState [0, x.length] (initMem x) 0) = some (o, st_Q', c_Q) := by
    rw [exec_noRand hDet fuel hbody_noRand (ω₂ := fun _ => false)]
    exact hexecQ
  have hcw1 : 1 ≤ impl.cw := by have := impl.hcw; omega
  have hpow := pow_lt_two_pow_wordSize hcw1 x
  have hx_lt : x.length < 2 ^ w' := by
    have h1 : x.length < x.length + x.foldr max 0 + 2 := by omega
    have h2 : x.length + x.foldr max 0 + 2 ≤ (x.length + x.foldr max 0 + 2) ^ impl.cw := by
      simpa using Nat.pow_le_pow_right (by omega) hcw1
    exact lt_trans (lt_of_lt_of_le h1 h2) hpow
  have hm_lt : ∀ a, initMem x a < 2 ^ w' := by
    intro a
    by_cases ha : a < x.length
    · have h1 : initMem x a = x[a]'ha := List.getD_eq_getElem x 0 ha
      have h2 : x[a]'ha ≤ x.foldr max 0 := le_foldr_max_of_mem (List.getElem_mem ha)
      have h3 : x.foldr max 0 < (x.length + x.foldr max 0 + 2) ^ impl.cw := by
        have hlt : x.foldr max 0 < x.length + x.foldr max 0 + 2 := by omega
        have hle : x.length + x.foldr max 0 + 2 ≤ (x.length + x.foldr max 0 + 2) ^ impl.cw := by
          simpa using Nat.pow_le_pow_right (by omega) hcw1
        exact lt_of_lt_of_le hlt hle
      rw [h1]
      exact lt_trans (lt_of_le_of_lt h2 h3) hpow
    · have h0 : initMem x a = 0 := List.getD_eq_default x 0 (by omega)
      rw [h0]; exact Nat.zero_lt_of_lt hx_lt
  have hregs_lt : ∀ r, (startState [0, x.length] (initMem x) 0).regs r < 2 ^ w' := by
    intro r
    rcases r with _ | _ | r
    · simp [startState]
    · simp [startState]; exact hx_lt
    · simp [startState]
  set h := guestBase - 1
  have hh1 : h + 1 = guestBase := by omega
  have hmem_agree : ∀ a < 2 ^ w', st_H.mem (h + 1 + a) = (startState [0, x.length] (initMem x) 0).mem a := by
    intro a _
    rw [hh1]
    by_cases ha : a < x.length
    · have h2 : (startState [0, x.length] (initMem x) 0).mem a = x[a]'ha := by
        simpa [startState, initMem] using List.getD_eq_getElem x 0 ha
      rw [h2]
      exact hmem_in a ha
    · have h1 : guestBase + x.length ≤ guestBase + a := by omega
      have h2 := hmem_zero (guestBase + a) h1
      have h3 : initMem x a = 0 := List.getD_eq_default x 0 (by omega)
      simpa [startState, h3] using h2
  obtain ⟨st_H', c_H, k', hRunH, hcH_le, _, _, _, _, _, _, hmemH_agree, hframeH, hposQ, hposH⟩ :=
    Link.runs_relocStmt (pos₀ := st_H.pos)
      hpReloc hw' (by rw [hh1]; exact hgBw) hw4
      fuel body (startState [0, x.length] (initMem x) 0) st_H 0 o st_Q' c_Q
      (stmt_regBound_le_program hQ0)
      (by rw [hh1]; exact hreg_base) hreg_W hregs_arg hregs_lt hm_lt hmem_agree (by simp [startState])
      (by simp) hexec_sub
  have hmem_reloc : ∀ a < 2 ^ w', st_H'.mem (guestBase + a) = st_Q'.mem a := by
    intro a ha; simpa [hh1] using hmemH_agree a ha
  have hzH : ZeroFrom st_H'.mem (guestBase + o.value) := by
    intro addr haddr
    by_cases hwin : addr < guestBase + 2 ^ w'
    · set a := addr - guestBase
      have ha_lt : a < 2 ^ w' := Nat.sub_lt_left_of_lt_add (by omega) hwin
      have ha_eq : guestBase + a = addr := Nat.add_sub_of_le (by omega)
      rw [← ha_eq, hmem_reloc a ha_lt]
      exact hzQ a (Nat.le_sub_of_add_le' haddr)
    · have hfr := hframeH addr (Or.inr (by rw [hh1]; exact Nat.le_of_not_lt hwin))
      rw [hfr]
      exact hmem_zero addr (Nat.le_trans (Nat.add_le_add_left hx_le guestBase) haddr)
  have hOutH := sparsifyOutRelocAt_of_reloc (le_of_lt ho_lt) hmem_reloc hOutQ
  have hPosEq : st_H'.pos = st_H.pos := by
    have hq0 : st_Q'.pos = 0 := by
      have h1 := exec_pos_of_noRand hDet fuel hbody_noRand hexecQ
      simpa [startState] using h1
    have hw'_pos : 0 < w' := by
      change 0 < impl.cw * (Nat.log 2 (x.length + x.foldr max 0 + 2) + 1)
      exact Nat.mul_pos (by have := impl.hcw; omega) (Nat.succ_pos _)
    have hk0 : k' = 0 := by
      rw [hq0] at hposQ
      exact (Nat.mul_eq_zero.mp hposQ.symm).resolve_right (Nat.ne_of_gt hw'_pos)
    rw [hposH, hk0, zero_mul, add_zero]
  exact ⟨body, o, st_H', c_H, cJtilde, kept, embJJtilde, c_Q, hQ0, hpReloc 0 body hQ0,
    hRunH, hcH_le, hCostQ, hx_le, ho_lt, hzH, hProp, hOutH,
    by rw [hCS], by rw [hCS], by rw [hCS],
    fun addr haddr => hframeH addr (by simpa [hh1] using haddr),
    hPosEq⟩

end

end MinCostFlow.DynSpanner.Program
