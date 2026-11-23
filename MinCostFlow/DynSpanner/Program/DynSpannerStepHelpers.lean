module

public import MinCostFlow.DynSpanner.Program.DynSpannerInitCost
public import MinCostFlow.DynSpanner.StepTransition

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shared Endpoint-Congruence & Unsorted Batch Helpers (`DynSpannerStepHelpers`)

Pure bridge lemmas reused across `DynSpannerAffectedCover`, `DynSpannerAffected`,
`DynSpannerProj`, `DynSpannerStepRestart`, and `DynSpannerStepRebuild`:
* `canonicalSparsify_congr_ends` & `prefixWalk_congr_ends`: invariance under host graphs with
  identical `tail, head`.
* `diffBatch_perm_props`: unsorted `uhPref ++ uhDel' ++ uhIns'` matching `(step ...).UH` up to
  `List.Perm`, preserving `BatchIsValid`, `applyBatch`, and `batchEnc`.
* `batchBodyAt_append`, `batchBodyAt_singleton`: Word-RAM `BatchBodyAt` composition lemmas.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM
open MinCostFlow.Spanner
open MinCostFlow.DynSpanner

@[expose] public section

/-! ## `canonicalSparsify` and `prefixWalk` endpoint congruence -/

lemma walkVertices_congr_ends {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (u : ℕ) (P : List (ℕ × Bool)) :
    H₁.walkVertices u P = H₂.walkVertices u P := by
  induction P generalizing u with
  | nil => rfl
  | cons x xs ih =>
    have hdst : H₁.dst x = H₂.dst x := by
      cases x.2 <;> simp [MGraph.dst, ht, hh]
    simp only [MGraph.walkVertices, List.map_cons]
    congr 1
    rw [hdst]
    simpa [MGraph.walkVertices] using ih (H₂.dst x)

lemma usedHVerts_congr_ends {H₁ H₂ J : MGraph} (ht : H₁.tail = H₂.tail) (hh : H₁.head = H₂.head)
    (emb : MinCostFlow.Embedding) :
    usedHVerts H₁ J emb = usedHVerts H₂ J emb := by
  unfold usedHVerts
  congr 1
  ext v
  simp only [Finset.mem_biUnion, List.mem_toFinset]
  constructor <;> rintro ⟨e, he, hv⟩ <;> refine ⟨e, he, ?_⟩
  · rwa [← walkVertices_congr_ends ht hh (J.tail e) (emb e)]
  · rwa [walkVertices_congr_ends ht hh (J.tail e) (emb e)]

lemma toCitedH_congr_ends {H₁ H₂ J : MGraph} (ht : H₁.tail = H₂.tail) (hh : H₁.head = H₂.head)
    (emb : MinCostFlow.Embedding) :
    toCitedH H₁ J emb = toCitedH H₂ J emb := by
  have hv : hVerts H₁ J emb = hVerts H₂ J emb := by
    unfold hVerts
    rw [usedHVerts_congr_ends ht hh emb]
  unfold toCitedH
  rw [hv, ht, hh]

lemma embToCited_congr_ends {H₁ H₂ J : MGraph} (ht : H₁.tail = H₂.tail) (hh : H₁.head = H₂.head)
    (emb : MinCostFlow.Embedding) :
    embToCited H₁ J emb = embToCited H₂ J emb := by
  funext j
  have hv : hVerts H₁ J emb = hVerts H₂ J emb := by
    unfold hVerts
    rw [usedHVerts_congr_ends ht hh emb]
  unfold embToCited walkToCited
  simp only [hv, walkVertices_congr_ends ht hh]

lemma canonSparsifyInput_congr_ends {H₁ H₂ J : MGraph} (ht : H₁.tail = H₂.tail)
    (hh : H₁.head = H₂.head) (emb : MinCostFlow.Embedding) :
    canonSparsifyInput H₁ J emb = canonSparsifyInput H₂ J emb := by
  unfold canonSparsifyInput
  rw [toCitedH_congr_ends ht hh emb, embToCited_congr_ends ht hh emb]

private lemma walkAt_inj' {mem : ℕ → ℕ} {a : ℕ} {w₁ w₂ : MinCostFlow.Spanner.Walk}
    (h₁ : MinCostFlow.Spanner.WalkAt mem a w₁) (h₂ : MinCostFlow.Spanner.WalkAt mem a w₂) : w₁ = w₂ := by
  have hv_len : w₁.verts.length = w₂.verts.length := by
    have m1 := h₁ 0 (by simp [MinCostFlow.Spanner.Walk.encode])
    have m2 := h₂ 0 (by simp [MinCostFlow.Spanner.Walk.encode])
    simp only [MinCostFlow.Spanner.Walk.encode, List.cons_append, List.getElem_cons_zero] at m1 m2
    omega
  have hverts : w₁.verts = w₂.verts := by
    refine List.ext_getElem hv_len fun i hi₁ hi₂ => ?_
    have m1 := h₁ (i + 1) (by simp [MinCostFlow.Spanner.Walk.encode]; omega)
    have m2 := h₂ (i + 1) (by simp [MinCostFlow.Spanner.Walk.encode]; omega)
    simp only [MinCostFlow.Spanner.Walk.encode, List.cons_append, List.getElem_cons_succ,
      List.getElem_append_left hi₁, List.getElem_append_left hi₂] at m1 m2
    omega
  have he_len : w₁.edges.length = w₂.edges.length := by
    have m1 := h₁ (w₁.verts.length + 1) (by simp [MinCostFlow.Spanner.Walk.encode])
    have m2 := h₂ (w₁.verts.length + 1) (by simp [MinCostFlow.Spanner.Walk.encode, hv_len])
    simp only [MinCostFlow.Spanner.Walk.encode, List.cons_append, List.getElem_cons_succ] at m1 m2
    simp [List.getElem_append_right (le_refl _), hv_len] at m1 m2
    omega
  have hedges : w₁.edges = w₂.edges := by
    refine List.ext_getElem he_len fun i hi₁ hi₂ => ?_
    have m1 := h₁ (w₁.verts.length + i + 2) (by simp [MinCostFlow.Spanner.Walk.encode]; omega)
    have m2 := h₂ (w₁.verts.length + i + 2) (by simp [MinCostFlow.Spanner.Walk.encode, hv_len]; omega)
    simp only [MinCostFlow.Spanner.Walk.encode, List.cons_append, List.getElem_cons_succ] at m1 m2
    simp only [List.getElem_append_right (by omega : w₁.verts.length ≤ w₁.verts.length + i + 1)] at m1
    simp only [List.getElem_append_right (by omega : w₂.verts.length ≤ w₁.verts.length + i + 1)] at m2
    have h1' : w₁.verts.length + i + 1 - w₁.verts.length = i + 1 := by omega
    have h2' : w₁.verts.length + i + 1 - w₂.verts.length = i + 1 := by omega
    simp [h1'] at m1
    simp [h2'] at m2
    omega
  cases w₁; cases w₂; simp_all

private lemma listAt_inj {mem : ℕ → ℕ} {a : ℕ} {xs ys : List ℕ}
    (hlen : xs.length = ys.length)
    (h₁ : ListAt mem a xs) (h₂ : ListAt mem a ys) : xs = ys := by
  refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
  have hm1 := h₁ i hi₁
  have hm2 := h₂ i hi₂
  omega

private lemma reloc_eq_aux {mem₁ mem₂ : ℕ → ℕ} {x₁ x₂ : List ℕ} {v₁ v₂ mJ : ℕ}
    (hm : mem₁ = mem₂) (hx : x₁ = x₂)
    {cJ₁ cJ₂ : MinCostFlow.Cited.Graph} {k₁ k₂ : List ℕ} {e₁ e₂ : ℕ → MinCostFlow.Spanner.Walk}
    (h1 : SparsifyOutRelocAt mem₁ 0 x₁.length v₁ mJ cJ₁ k₁ e₁)
    (h2 : SparsifyOutRelocAt mem₂ 0 x₂.length v₂ mJ cJ₂ k₂ e₂) :
    cJ₁ = cJ₂ ∧ k₁ = k₂ ∧ ∀ j < mJ, e₁ j = e₂ j := by
  subst hm hx
  rcases h1 with ⟨_, _, _, _, hG₁, hK₁, hE₁⟩
  rcases h2 with ⟨_, _, _, _, hG₂, hK₂, hE₂⟩
  have hcJ : cJ₁ = cJ₂ :=
    (graphAt_iff_readGraph.mp hG₁).symm.trans (graphAt_iff_readGraph.mp hG₂)
  have hk_len : k₁.length = k₂.length := by
    have hm1 := hK₁ 0 (by simp)
    have hm2 := hK₂ 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hm1 hm2
    omega
  have hk : k₁ = k₂ := (List.cons.inj (listAt_inj (by simp [hk_len]) hK₁ hK₂)).2
  have he : ∀ j < mJ, e₁ j = e₂ j := fun j hj => by
    have ha := (hE₁ j hj).2
    have hb := (hE₂ j hj).2
    simp only [zero_add] at ha hb
    exact walkAt_inj' ha hb
  exact ⟨hcJ, hk, he⟩

/-- Replaces `H₁` by `H₂` with identical `tail, head` inside `canonicalSparsify impl`. -/
theorem canonicalSparsify_congr_ends (impl : SparsifyImpl)
    {H₁ H₂ J : MGraph} {emb : MinCostFlow.Embedding}
    (ht : H₁.tail = H₂.tail) (hh : H₁.head = H₂.head)
    (hH₁ : H₁.IsValid) (hH₂ : H₂.IsValid) (hJ : J.IsValid)
    (hLen : J.E.Nonempty → 1 ≤ emb.length J)
    (hemb₁ : emb.IsEmbedding J H₁) (hemb₂ : emb.IsEmbedding J H₂) :
    canonicalSparsify impl H₁ J emb = canonicalSparsify impl H₂ J emb := by
  by_cases hJn : 1 ≤ J.n
  · have hV₁ : CanonicalSparsifyValid impl H₁ J emb := ⟨hJn, hH₁, hJ, hLen, hemb₁⟩
    have hV₂ : CanonicalSparsifyValid impl H₂ J emb := ⟨hJn, hH₂, hJ, hLen, hemb₂⟩
    have hx_eq : canonSparsifyInput H₁ J emb = canonSparsifyInput H₂ J emb :=
      canonSparsifyInput_congr_ends ht hh emb
    obtain ⟨body₁, o₁, st₁', cost₁, cJ₁, kept₁, emb₁, hp₁, hr₁, _, _, _, _, hOut₁, _⟩ :=
      canonicalGuestRun_exists impl J.m hH₁ hJ (le_refl _) hLen hemb₁
    obtain ⟨body₂, o₂, st₂', cost₂, cJ₂, kept₂, emb₂, hp₂, hr₂, _, _, _, _, hOut₂, _⟩ :=
      canonicalGuestRun_exists impl J.m hH₂ hJ (le_refl _) hLen hemb₂
    have hbody_eq : body₁ = body₂ := Option.some.inj (hp₁.symm.trans hp₂)
    have hr₂' : Runs (wordSize impl.cw (canonSparsifyInput H₁ J emb)) impl.program (fun _ => false)
        body₁ (startState [0, (canonSparsifyInput H₁ J emb).length]
          (initMem (canonSparsifyInput H₁ J emb)) 0) o₂ st₂' cost₂ := by
      rw [hbody_eq]
      simpa [← hx_eq] using hr₂
    obtain ⟨_, hst_eq, hcost_eq⟩ := Runs.det hr₁ hr₂'
    obtain ⟨hcJ_eq, hK_eq, hEmb_eq⟩ :=
      reloc_eq_aux (congrArg State.mem hst_eq) hx_eq hOut₁ hOut₂
    have hemb_fn : citedEmbToMGraph J cJ₁ kept₁ emb₁ = citedEmbToMGraph J cJ₂ kept₂ emb₂ := by
      funext e
      unfold citedEmbToMGraph
      split_ifs with he
      · have hidx : (vertsOf J.E).idxOf e < (toCitedJ J).m := by
          rw [toCitedJ_m J]
          change (vertsOf J.E).idxOf e < J.E.card
          rw [← vertsOf_length J.E]
          exact List.idxOf_lt_length_of_mem (mem_vertsOf.mpr he)
        have hcJ' : cJ₁ = cJ₂ := hcJ_eq
        have hK' : kept₁ = kept₂ := hK_eq
        have hE' : emb₁ ((vertsOf J.E).idxOf e) = emb₂ ((vertsOf J.E).idxOf e) := hEmb_eq _ hidx
        rw [hcJ', hK', hE']
      · rfl
    have h1 := canonicalSparsify_eq_of_run hV₁ hp₁ hr₁ hOut₁
    have h2 := canonicalSparsify_eq_of_run hV₂ hp₂ hr₂ hOut₂
    have hK_eq' : kept₁ = kept₂ := hK_eq
    have hcost_eq' : cost₁ = cost₂ := hcost_eq
    rw [h1, h2, hemb_fn, hK_eq', hcost_eq']
  · have hV₁ : ¬ CanonicalSparsifyValid impl H₁ J emb := fun h => hJn h.1
    have hV₂ : ¬ CanonicalSparsifyValid impl H₂ J emb := fun h => hJn h.1
    simp [canonicalSparsify, hV₁, hV₂]

/-- `prefixWalk` only reads `H.tail` and `H.head`, so subgraphs with identical endpoints match. -/
theorem prefixWalk_congr_ends {H₁ H₂ : MGraph} (ht : H₁.tail = H₂.tail) (hh : H₁.head = H₂.head)
    (u : ℕ) (W : List (ℕ × Bool)) (S : Finset ℕ) :
    prefixWalk H₁ u W S = prefixWalk H₂ u W S := by
  induction W generalizing u with
  | nil => rfl
  | cons x xs ih =>
    have hdst : H₁.dst x = H₂.dst x := by
      cases x.2 <;> simp [MGraph.dst, ht, hh]
    unfold prefixWalk
    split_ifs with hu
    · rfl
    · simp only [hdst, ih (H₂.dst x)]

/-! ## Unsorted Differential Batch (`uhPref ++ uhDel' ++ uhIns'`) -/

private lemma batchIsValid_deletes_perm :
    ∀ (l : List ℕ) (H : MGraph),
      H.IsValid → l.Nodup → (∀ e ∈ l, e ∈ H.E) →
      let H' := H.applyBatch (l.map Update.delete)
      H.BatchIsValid (l.map Update.delete) ∧
      H'.IsValid ∧
      H'.V = H.V ∧
      H'.E = H.E \ l.toFinset ∧
      H'.tail = H.tail ∧
      H'.head = H.head ∧
      H.batchEnc (l.map Update.delete) = l.length
  | [], H, hV, _, _ => by
    simp [MGraph.BatchIsValid, MGraph.applyBatch, MGraph.batchEnc, hV]
  | a :: l, H, hV, hnod, hmem => by
    simp only [List.nodup_cons] at hnod
    have haE : a ∈ H.E := hmem a List.mem_cons_self
    have hV1 : (H.applyUpdate (.delete a)).IsValid :=
      isValid_applyUpdate_of_delOrSplit hV haE (by simp [isDelOrSplit])
    have hmem1 : ∀ e ∈ l, e ∈ (H.applyUpdate (.delete a)).E := fun e he => by
      have hne : e ≠ a := fun h => hnod.1 (h ▸ he)
      simp [MGraph.applyUpdate, hne, hmem e (List.mem_cons_of_mem _ he)]
    have ih := batchIsValid_deletes_perm l (H.applyUpdate (.delete a)) hV1 hnod.2 hmem1
    rcases ih with ⟨hBV1, hV', hV_eq, hE_eq, ht_eq, hh_eq, henc⟩
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, MGraph.BatchIsValid,
      MGraph.batchEnc, List.length_cons] at hV_eq hE_eq ht_eq hh_eq henc ⊢
    refine ⟨⟨haE, hBV1⟩, hV', by simpa [MGraph.applyUpdate] using hV_eq, ?_,
      by simpa [MGraph.applyUpdate] using ht_eq, by simpa [MGraph.applyUpdate] using hh_eq, ?_⟩
    · rw [hE_eq]
      simp only [MGraph.applyUpdate, List.toFinset_cons]
      ext e
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
      tauto
    · simp only [MGraph.updateEnc] at henc ⊢
      omega

private lemma batchIsValid_inserts_perm (G' : MGraph) (hVG' : G'.IsValid) :
    ∀ (l : List ℕ) (H : MGraph),
      H.IsValid → H.V = G'.V → l.Nodup → (∀ e ∈ l, e ∈ G'.E ∧ e ∉ H.E) →
      let bat := l.map fun e => Update.insert e (G'.tail e) (G'.head e)
      let H' := H.applyBatch bat
      H.BatchIsValid bat ∧
      H'.IsValid ∧
      H'.V = H.V ∧
      H'.E = H.E ∪ l.toFinset ∧
      (∀ e : ℕ, H'.tail e = if e ∈ l then G'.tail e else H.tail e) ∧
      (∀ e : ℕ, H'.head e = if e ∈ l then G'.head e else H.head e) ∧
      H.batchEnc bat = l.length
  | [], H, hV, _, _, _ => by
    simp [MGraph.BatchIsValid, MGraph.applyBatch, MGraph.batchEnc, hV]
  | a :: l, H, hV, hHV, hnod, hmem => by
    simp only [List.nodup_cons] at hnod
    obtain ⟨haG', haH⟩ := hmem a List.mem_cons_self
    obtain ⟨hat, hah⟩ := hVG' a haG'
    let u := Update.insert a (G'.tail a) (G'.head a)
    have hu : H.UpdateIsValid u := ⟨haH, hHV ▸ hat, hHV ▸ hah⟩
    have hV1 : (H.applyUpdate u).IsValid := isValid_applyUpdate_any hV hu
    have hHV1 : (H.applyUpdate u).V = G'.V := by simpa [u, MGraph.applyUpdate] using hHV
    have hmem1 : ∀ e ∈ l, e ∈ G'.E ∧ e ∉ (H.applyUpdate u).E := fun e he => by
      have hne : e ≠ a := fun h => hnod.1 (h ▸ he)
      obtain ⟨heG', heH⟩ := hmem e (List.mem_cons_of_mem _ he)
      exact ⟨heG', by simpa [u, MGraph.applyUpdate, Finset.mem_insert, hne] using heH⟩
    have ih := batchIsValid_inserts_perm G' hVG' l (H.applyUpdate u) hV1 hHV1 hnod.2 hmem1
    rcases ih with ⟨hBV1, hV', hV_eq, hE_eq, ht_eq, hh_eq, henc⟩
    simp only [List.map_cons, MGraph.applyBatch, List.foldl_cons, MGraph.BatchIsValid,
      MGraph.batchEnc, List.length_cons] at hV_eq hE_eq ht_eq hh_eq henc ⊢
    refine ⟨⟨hu, hBV1⟩, hV', by simpa [u, MGraph.applyUpdate] using hV_eq, ?_, ?_, ?_, ?_⟩
    · rw [hE_eq]
      simp only [u, MGraph.applyUpdate, List.toFinset_cons]
      ext e
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · intro e
      rw [ht_eq e]
      simp only [List.mem_cons, u, MGraph.applyUpdate, Function.update]
      by_cases hel : e ∈ l
      · have hne : e ≠ a := fun h => hnod.1 (h ▸ hel)
        simp [hel]
      · by_cases hea : e = a <;> simp [hel, hea]
    · intro e
      rw [hh_eq e]
      simp only [List.mem_cons, u, MGraph.applyUpdate, Function.update]
      by_cases hel : e ∈ l
      · have hne : e ≠ a := fun h => hnod.1 (h ▸ hel)
        simp [hel]
      · by_cases hea : e = a <;> simp [hel, hea]
    · simp only [MGraph.updateEnc] at henc ⊢
      dsimp only [u] at henc
      omega

private lemma mgraph_eq_of_props {H₁ H₂ : MGraph} (hV : H₁.V = H₂.V) (hE : H₁.E = H₂.E)
    (ht : ∀ e, H₁.tail e = H₂.tail e) (hh : ∀ e, H₁.head e = H₂.head e) : H₁ = H₂ := by
  have ht' : H₁.tail = H₂.tail := funext ht
  have hh' : H₁.head = H₂.head := funext hh
  cases H₁; cases H₂; simp_all

private lemma batchEnc_append_gen :
    ∀ (U₁ U₂ : List Update) (G : MGraph),
      G.batchEnc (U₁ ++ U₂) = G.batchEnc U₁ + (G.applyBatch U₁).batchEnc U₂
  | [], _, _ => by simp [MGraph.batchEnc, MGraph.applyBatch]
  | u :: U₁, U₂, G => by
    simp only [List.cons_append, MGraph.batchEnc]
    have ih := batchEnc_append_gen U₁ U₂ (G.applyUpdate u)
    change G.updateEnc u + (G.applyUpdate u).batchEnc (U₁ ++ U₂) =
      G.updateEnc u + (G.applyUpdate u).batchEnc U₁ + ((G.applyUpdate u).applyBatch U₁).batchEnc U₂
    rw [ih, Nat.add_assoc]

/-- Unsorted differential batch emission (`uhPref ++ uhDel' ++ uhIns'`) agrees up to `List.Perm`
with `(step ...).UH`, yields the exact same graph `H' = H.applyBatch UH`, preserves
`BatchIsValid`, and has identical `batchEnc`. -/
theorem diffBatch_perm_props {G H : MGraph} (hVG : G.IsValid) (hSub : G.IsSubgraph H)
    (hHV : H.V = G.V) {u : Update} (hu : G.UpdateIsValid u) (hdu : isDelOrSplit u)
    {H_new_E : Finset ℕ} (hNewSub : H_new_E ⊆ (G.applyUpdate u).E)
    {lDel lIns : List ℕ} (hDel_nd : lDel.Nodup)
    (hDel_mem : ∀ e, e ∈ lDel ↔ e ∈ (H.applyBatch (restrictUpdate u H)).E \ H_new_E)
    (hIns_nd : lIns.Nodup)
    (hIns_mem : ∀ e, e ∈ lIns ↔ e ∈ H_new_E \ (H.applyBatch (restrictUpdate u H)).E) :
    let G' := G.applyUpdate u
    let uhPref := restrictUpdate u H
    let H_mid := H.applyBatch uhPref
    let uhDel' := lDel.map Update.delete
    let uhIns' := lIns.map fun e => Update.insert e (G'.tail e) (G'.head e)
    let uh' := uhPref ++ uhDel' ++ uhIns'
    let uhDelS := ((H_mid.E \ H_new_E).sort (· ≤ ·)).map Update.delete
    let uhInsS := ((H_new_E \ H_mid.E).sort (· ≤ ·)).map fun e =>
      Update.insert e (G'.tail e) (G'.head e)
    let uhS := uhPref ++ uhDelS ++ uhInsS
    uh'.Perm uhS ∧
    H.BatchIsValid uh' ∧
    H.applyBatch uh' = H.applyBatch uhS ∧
    H.batchEnc uh' = H.batchEnc uhS := by
  intro G' uhPref H_mid uhDel' uhIns' uh' uhDelS uhInsS uhS
  have hr := isSubgraph_restrictUpdate hSub hHV hu hdu
  rcases hr with ⟨hBV_pref, hSub_mid, hV_mid, _, _, _⟩
  have hVG' : G'.IsValid := isValid_applyUpdate_of_delOrSplit hVG hu hdu
  have hV_Hmid : H_mid.IsValid := by
    intro e he
    have heG' := hSub_mid.2.1 he
    have hv := hVG' e heG'
    rw [← (hSub_mid.2.2 e he).1, ← (hSub_mid.2.2 e he).2, ← hV_mid] at hv
    exact hv
  set lDelS := (H_mid.E \ H_new_E).sort (· ≤ ·)
  set lInsS := (H_new_E \ H_mid.E).sort (· ≤ ·)
  have hDelS_nd : lDelS.Nodup := Finset.sort_nodup _ _
  have hInsS_nd : lInsS.Nodup := Finset.sort_nodup _ _
  have hDelS_mem : ∀ e, e ∈ lDelS ↔ e ∈ H_mid.E \ H_new_E := fun e => Finset.mem_sort _
  have hInsS_mem : ∀ e, e ∈ lInsS ↔ e ∈ H_new_E \ H_mid.E := fun e => Finset.mem_sort _
  have hPerm_del : lDel.Perm lDelS :=
    (List.perm_ext_iff_of_nodup hDel_nd hDelS_nd).mpr fun e => by
      exact (hDel_mem e).trans (hDelS_mem e).symm
  have hPerm_ins : lIns.Perm lInsS :=
    (List.perm_ext_iff_of_nodup hIns_nd hInsS_nd).mpr fun e => by
      exact (hIns_mem e).trans (hInsS_mem e).symm
  have hPerm : uh'.Perm uhS :=
    (List.Perm.append_left uhPref (hPerm_del.map Update.delete)).append
      (hPerm_ins.map fun e => Update.insert e (G'.tail e) (G'.head e))
  have hDel_E : ∀ e ∈ lDel, e ∈ H_mid.E := fun e he => (Finset.mem_sdiff.mp ((hDel_mem e).mp he)).1
  have hDelS_E : ∀ e ∈ lDelS, e ∈ H_mid.E := fun e he => (Finset.mem_sdiff.mp ((hDelS_mem e).mp he)).1
  obtain ⟨hBV_d1, hVd1, hV_d1, hE_d1, ht_d1, hh_d1, henc_d1⟩ :=
    batchIsValid_deletes_perm lDel H_mid hV_Hmid hDel_nd hDel_E
  obtain ⟨_, hVdS, hV_dS, hE_dS, ht_dS, hh_dS, henc_dS⟩ :=
    batchIsValid_deletes_perm lDelS H_mid hV_Hmid hDelS_nd hDelS_E
  have hIns_E : ∀ e ∈ lIns, e ∈ G'.E ∧ e ∉ (H_mid.applyBatch uhDel').E := fun e he => by
    obtain ⟨heN, heM⟩ := Finset.mem_sdiff.mp ((hIns_mem e).mp he)
    refine ⟨hNewSub heN, ?_⟩
    rw [hE_d1]
    intro hmem
    exact heM (Finset.mem_sdiff.mp hmem).1
  have hInsS_E : ∀ e ∈ lInsS, e ∈ G'.E ∧ e ∉ (H_mid.applyBatch uhDelS).E := fun e he => by
    obtain ⟨heN, heM⟩ := Finset.mem_sdiff.mp ((hInsS_mem e).mp he)
    refine ⟨hNewSub heN, ?_⟩
    rw [hE_dS]
    intro hmem
    exact heM (Finset.mem_sdiff.mp hmem).1
  obtain ⟨hBV_i1, _, hV_i1, hE_i1, ht_i1, hh_i1, henc_i1⟩ :=
    batchIsValid_inserts_perm G' hVG' lIns (H_mid.applyBatch uhDel') hVd1
      (by rw [hV_d1, hV_mid]) hIns_nd hIns_E
  obtain ⟨_, _, hV_iS, hE_iS, ht_iS, hh_iS, henc_iS⟩ :=
    batchIsValid_inserts_perm G' hVG' lInsS (H_mid.applyBatch uhDelS) hVdS
      (by rw [hV_dS, hV_mid]) hInsS_nd hInsS_E
  have hBV' : H.BatchIsValid uh' := by
    rw [show uh' = (uhPref ++ uhDel') ++ uhIns' from rfl, batchIsValid_append, batchIsValid_append]
    exact ⟨⟨hBV_pref, hBV_d1⟩, by rw [← applyBatch_append] at hBV_i1; exact hBV_i1⟩
  have hApply_eq : H.applyBatch uh' = H.applyBatch uhS := by
    rw [show uh' = (uhPref ++ uhDel') ++ uhIns' from rfl, applyBatch_append, applyBatch_append]
    rw [show uhS = (uhPref ++ uhDelS) ++ uhInsS from rfl, applyBatch_append, applyBatch_append]
    change (H_mid.applyBatch uhDel').applyBatch uhIns' =
      (H_mid.applyBatch uhDelS).applyBatch uhInsS
    refine mgraph_eq_of_props ?_ ?_ ?_ ?_
    · rw [hV_i1, hV_iS, hV_d1, hV_dS]
    · rw [hE_i1, hE_iS, hE_d1, hE_dS]
      ext e
      simp only [Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, hDel_mem, hIns_mem,
        hDelS_mem, hInsS_mem]
      tauto
    · intro e
      rw [ht_i1 e, ht_iS e, ht_d1, ht_dS]
      have heq : (e ∈ lIns) ↔ (e ∈ lInsS) := (hIns_mem e).trans (hInsS_mem e).symm
      by_cases h1 : e ∈ lIns
      · simp [h1, heq.mp h1]
      · simp [h1, mt heq.mpr h1]
    · intro e
      rw [hh_i1 e, hh_iS e, hh_d1, hh_dS]
      have heq : (e ∈ lIns) ↔ (e ∈ lInsS) := (hIns_mem e).trans (hInsS_mem e).symm
      by_cases h1 : e ∈ lIns
      · simp [h1, heq.mp h1]
      · simp [h1, mt heq.mpr h1]
  have hEnc_eq : H.batchEnc uh' = H.batchEnc uhS := by
    rw [show uh' = (uhPref ++ uhDel') ++ uhIns' from rfl, batchEnc_append_gen, batchEnc_append_gen]
    rw [show uhS = (uhPref ++ uhDelS) ++ uhInsS from rfl, batchEnc_append_gen, batchEnc_append_gen]
    change H.batchEnc uhPref + H_mid.batchEnc uhDel' +
        (H.applyBatch (uhPref ++ uhDel')).batchEnc uhIns' =
      H.batchEnc uhPref + H_mid.batchEnc uhDelS +
        (H.applyBatch (uhPref ++ uhDelS)).batchEnc uhInsS
    rw [applyBatch_append, applyBatch_append]
    change H.batchEnc uhPref + H_mid.batchEnc uhDel' + (H_mid.applyBatch uhDel').batchEnc uhIns' =
      H.batchEnc uhPref + H_mid.batchEnc uhDelS + (H_mid.applyBatch uhDelS).batchEnc uhInsS
    rw [henc_d1, henc_dS, henc_i1, henc_iS, hPerm_del.length_eq, hPerm_ins.length_eq]
  exact ⟨hPerm, hBV', hApply_eq, hEnc_eq⟩

/-! ## Word-RAM `BatchBodyAt` Composition Helpers -/

lemma batchBodyAt_append :
    ∀ {mem : ℕ → ℕ} {a len₁ len₂ : ℕ} {G : MGraph} {U₁ U₂ : List Update},
      BatchBodyAt mem a G U₁ len₁ →
      BatchBodyAt mem (a + len₁) (G.applyBatch U₁) U₂ len₂ →
      BatchBodyAt mem a G (U₁ ++ U₂) (len₁ + len₂)
  | _, _, _, _, G, [], _, h1, h2 => by
    rw [BatchBodyAt.eq_1] at h1; subst h1
    simpa [MGraph.applyBatch] using h2
  | mem, a, len₁, len₂, G, u :: U₁, U₂, h1, h2 => by
    rw [BatchBodyAt.eq_2] at h1
    rcases h1 with ⟨l, hl, hu, hrest⟩
    rw [List.cons_append, BatchBodyAt.eq_2]
    refine ⟨l, by omega, hu, ?_⟩
    have hrest2 := batchBodyAt_append hrest (by
      simpa [MGraph.applyBatch, List.foldl_cons, Nat.add_assoc,
        show l + (len₁ - l) = len₁ from Nat.add_sub_cancel' hl] using h2)
    simpa [Nat.sub_add_comm hl] using hrest2

lemma batchBodyAt_singleton {mem : ℕ → ℕ} {a len : ℕ} {G : MGraph} {u : Update}
    (hu : UpdateAt mem a G u len) :
    BatchBodyAt mem a G [u] len := by
  rw [BatchBodyAt.eq_2]
  exact ⟨len, le_rfl, hu, by rw [BatchBodyAt.eq_1]; omega⟩

lemma batchBodyAt_agree {mem₁ mem₂ : ℕ → ℕ} :
    ∀ {a len : ℕ} {G : MGraph} {U : List Update},
      (∀ i < len, mem₁ (a + i) = mem₂ (a + i)) →
      BatchBodyAt mem₁ a G U len →
      BatchBodyAt mem₂ a G U len
  | _, _, _, [], hmem, h1 => by rw [BatchBodyAt.eq_1] at h1 ⊢; exact h1
  | a, len, G, u :: us, hmem, h1 => by
    rw [BatchBodyAt.eq_2] at h1 ⊢
    rcases h1 with ⟨l, hl, hu, hrest⟩
    refine ⟨l, hl, ?_, batchBodyAt_agree (fun i hi => by
      simpa [Nat.add_assoc] using hmem (l + i) (by omega)) hrest⟩
    have hu_eq : ∀ i < l, mem₁ (a + i) = mem₂ (a + i) := fun i hi => hmem i (by omega)
    cases u with
    | insert e x y =>
      rcases hu with ⟨rfl, hm⟩
      exact ⟨rfl, fun i hi => by rw [← hu_eq i (by simp at hi; omega)]; exact hm i hi⟩
    | delete e =>
      rcases hu with ⟨rfl, hm⟩
      exact ⟨rfl, fun i hi => by rw [← hu_eq i (by simp at hi; omega)]; exact hm i hi⟩
    | split v v' St Sh =>
      rcases hu with ⟨Lt, Lh, hndT, hndH, hmemT, hmemH, rfl, hm⟩ |
          ⟨Lt, Lh, hndT, hndH, hmemT, hmemH, rfl, hm⟩
      · left; exact ⟨Lt, Lh, hndT, hndH, hmemT, hmemH, rfl, fun i hi => by
          rw [← hu_eq i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)]
          exact hm i (by simpa using hi)⟩
      · right; exact ⟨Lt, Lh, hndT, hndH, hmemT, hmemH, rfl, fun i hi => by
          rw [← hu_eq i (by simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega)]
          exact hm i (by simpa using hi)⟩

end

end MinCostFlow.DynSpanner.Program
