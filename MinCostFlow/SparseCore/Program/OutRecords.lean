module

public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.DynSpanner.Program.DynGraphBatch
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract

/-!
# Runs of records in memory

The output step of piece P7 writes its output batch and its order edits one record at a time,
after the four words of the branch. So it needs a name for "the first `k` records written so
far", a rule that adds one record at the end, and a rule that says the records stay readable
when other cells change.

* For the batch this is `BatchBodyAt` of the graph layout. This file adds the rule for one more
  record at the end (`batchBodyAt_snoc`) and the full batch with its count word
  (`smallBatchAt_of_body`).
* For the edits, `EditsBody mem a ds words` says that the records from `a` decode to the edits
  `ds` in `words` words (`decodeOrdEdits`). This file proves the rule for one more record
  (`EditsBody.snoc`), the rule for other cells (`EditsBody.of_agree`, since a record is read only
  inside its own words), and the full list with its count word (`ordEditsAt_of_body`). It also
  reads back each kind of edit record (`decodeOrdEdit_drop`, …).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-! ## Edit records -/

/-- Every record tag in `count` consecutive edit records starting at `a` is at most `4`. -/
def EditsTagsLe4 (mem : ℕ → ℕ) : ℕ → ℕ → Prop
  | 0, _ => True
  | count + 1, a => mem a ≤ 4 ∧ EditsTagsLe4 mem count (a + (decodeOrdEdit mem a).2)

/-- The edit records from `a` decode to `ds`, in `words` words in all, with all tags `≤ 4`. -/
def EditsBody (mem : ℕ → ℕ) (a : ℕ) (ds : List OrdEdit) (words : ℕ) : Prop :=
  (decodeOrdEdits mem ds.length a).1 = ds ∧ ((decodeOrdEdits mem ds.length a).2).sum = words ∧
    EditsTagsLe4 mem ds.length a

theorem editsBody_nil (mem : ℕ → ℕ) (a : ℕ) : EditsBody mem a [] 0 := ⟨rfl, rfl, trivial⟩

/-- Reading `k + 1` records reads `k` records and then one more. -/
theorem decodeOrdEdits_snoc (mem : ℕ → ℕ) :
    ∀ k a, decodeOrdEdits mem (k + 1) a =
      ((decodeOrdEdits mem k a).1 ++
          [(decodeOrdEdit mem (a + ((decodeOrdEdits mem k a).2).sum)).1],
        (decodeOrdEdits mem k a).2 ++
          [(decodeOrdEdit mem (a + ((decodeOrdEdits mem k a).2).sum)).2])
  | 0, a => by simp [decodeOrdEdits]
  | k + 1, a => by
    have ih := decodeOrdEdits_snoc mem k (a + (decodeOrdEdit mem a).2)
    rw [decodeOrdEdits, ih]
    simp only [decodeOrdEdits, List.cons_append, List.sum_cons, Nat.add_assoc]

private theorem editsTagsLe4_snoc (mem : ℕ → ℕ) :
    ∀ k a, EditsTagsLe4 mem k a →
      mem (a + ((decodeOrdEdits mem k a).2).sum) ≤ 4 →
      EditsTagsLe4 mem (k + 1) a
  | 0, a, _, hlast => ⟨by simpa [decodeOrdEdits] using hlast, trivial⟩
  | k + 1, a, ⟨h0, hrest⟩, hlast =>
    ⟨h0, editsTagsLe4_snoc mem k (a + (decodeOrdEdit mem a).2) hrest (by
      simpa [decodeOrdEdits, List.sum_cons, Nat.add_assoc] using hlast)⟩

/-- **One more edit record.** -/
theorem EditsBody.snoc {mem : ℕ → ℕ} {a : ℕ} {ds : List OrdEdit} {words : ℕ}
    (hB : EditsBody mem a ds words) {d : OrdEdit} {l : ℕ}
    (hd : decodeOrdEdit mem (a + words) = (d, l)) (htag : mem (a + words) ≤ 4) :
    EditsBody mem a (ds ++ [d]) (words + l) := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hs := decodeOrdEdits_snoc mem ds.length a
  rw [h2, hd] at hs
  refine ⟨?_, ?_, ?_⟩
  · rw [List.length_append, List.length_singleton, hs, h1]
  · rw [List.length_append, List.length_singleton, hs, List.sum_append, h2]
    simp
  · rw [List.length_append, List.length_singleton]
    exact editsTagsLe4_snoc mem ds.length a h3 (by rwa [h2])

/-- An edit record is read only inside its own words. -/
theorem decodeOrdEdit_congr {mem mem' : ℕ → ℕ} {a : ℕ}
    (h : ∀ i < (decodeOrdEdit mem a).2, mem' (a + i) = mem (a + i)) :
    decodeOrdEdit mem' a = decodeOrdEdit mem a := by
  have h2 := decodeOrdEdit_words_ge_two mem a
  have e0 : mem' a = mem a := by simpa using h 0 (by omega)
  have e1 : mem' (a + 1) = mem (a + 1) := h 1 (by omega)
  unfold decodeOrdEdit at h ⊢
  rw [e0, e1]
  by_cases t0 : mem a = 0
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true t0)]
  simp only [ite_eq_right_of_eq_false _ _ (eq_false t0)] at h ⊢
  by_cases t12 : mem a = 1 ∨ mem a = 2
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true t12)] at h ⊢
    have e2 : mem' (a + 2) = mem (a + 2) := h 2 (by omega)
    have e3 : mem' (a + 3) = mem (a + 3) := h 3 (by omega)
    have hl : readList mem' (a + 4) (mem (a + 3)) = readList mem (a + 4) (mem (a + 3)) := by
      unfold readList
      apply List.map_congr_left
      intro i hi
      rw [List.mem_range] at hi
      simpa [Nat.add_assoc] using h (4 + i) (by omega)
    rw [e2, e3, hl]
  simp only [ite_eq_right_of_eq_false _ _ (eq_false t12)] at h ⊢
  by_cases t3 : mem a = 3
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true t3)] at h ⊢
    have e2 : mem' (a + 2) = mem (a + 2) := h 2 (by omega)
    have e3 : mem' (a + 3) = mem (a + 3) := h 3 (by omega)
    rw [e2, e3]
  · simp only [ite_eq_right_of_eq_false _ _ (eq_false t3)] at h ⊢
    have e2 : mem' (a + 2) = mem (a + 2) := h 2 (by omega)
    rw [e2]

/-- Records are read only inside their words. -/
theorem decodeOrdEdits_congr {mem mem' : ℕ → ℕ} :
    ∀ k a, (∀ i < ((decodeOrdEdits mem k a).2).sum, mem' (a + i) = mem (a + i)) →
      decodeOrdEdits mem' k a = decodeOrdEdits mem k a
  | 0, _, _ => rfl
  | k + 1, a, h => by
    have h1 : ∀ i < (decodeOrdEdit mem a).2, mem' (a + i) = mem (a + i) := by
      intro i hi
      apply h i
      simp only [decodeOrdEdits, List.sum_cons]
      omega
    have hd := decodeOrdEdit_congr h1
    have ih := decodeOrdEdits_congr (mem := mem) (mem' := mem') k (a + (decodeOrdEdit mem a).2)
      (by
        intro i hi
        have := h ((decodeOrdEdit mem a).2 + i) (by
          simp only [decodeOrdEdits, List.sum_cons]; omega)
        simpa [Nat.add_assoc] using this)
    simp only [decodeOrdEdits, hd, ih]

private theorem editsTagsLe4_congr {mem mem' : ℕ → ℕ} :
    ∀ k a, (∀ i < ((decodeOrdEdits mem k a).2).sum, mem' (a + i) = mem (a + i)) →
      EditsTagsLe4 mem k a → EditsTagsLe4 mem' k a
  | 0, _, _, _ => trivial
  | k + 1, a, h, ⟨h0, hrest⟩ => by
    have h1 : ∀ i < (decodeOrdEdit mem a).2, mem' (a + i) = mem (a + i) := fun i hi =>
      h i (by simp only [decodeOrdEdits, List.sum_cons]; omega)
    have h2 := decodeOrdEdit_words_ge_two mem a
    have e0 : mem' a = mem a := by simpa using h1 0 (by omega)
    have hd := decodeOrdEdit_congr h1
    refine ⟨by rw [e0]; exact h0, ?_⟩
    rw [hd]
    exact editsTagsLe4_congr k (a + (decodeOrdEdit mem a).2) (fun i hi => by
      have := h ((decodeOrdEdit mem a).2 + i) (by simp only [decodeOrdEdits, List.sum_cons]; omega)
      simpa [Nat.add_assoc] using this) hrest

/-- **The records stay readable** when only cells outside their words change. -/
theorem EditsBody.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {ds : List OrdEdit} {words : ℕ}
    (hB : EditsBody mem a ds words) (h : ∀ i < words, mem' (a + i) = mem (a + i)) :
    EditsBody mem' a ds words := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hc := decodeOrdEdits_congr ds.length a (by rw [h2]; exact h)
  exact ⟨by rw [hc, h1], by rw [hc, h2], editsTagsLe4_congr ds.length a (by rw [h2]; exact h) h3⟩

/-- **The full list of edits**: a count word, then the records. -/
theorem ordEditsAt_of_body {mem : ℕ → ℕ} {a : ℕ} {ds : List OrdEdit} {words : ℕ}
    (hc : mem a = ds.length) (hB : EditsBody mem (a + 1) ds words)
    (hw : words ≤ 5 * ordEditsEnc ds) : OrdEditsAt mem a ds (1 + words) := by
  obtain ⟨h1, h2, -⟩ := hB
  refine ⟨?_, ?_, by omega⟩
  · unfold readOrdEdits; rw [hc, h1]
  · rw [hc, h2]

private theorem decodeOrdEdit_words_lt {mem : ℕ → ℕ} {a vCap eCap B : ℕ}
    (htag : mem a ≤ 4)
    (hW : OrdEditsWithin vCap eCap [(decodeOrdEdit mem a).1])
    (h4 : 4 < B) (hV : vCap < B) (hE : 2 * eCap < B) (hlen : (decodeOrdEdit mem a).2 < B) :
    ∀ t < (decodeOrdEdit mem a).2, mem (a + t) < B := by
  have hw := hW _ List.mem_cons_self
  unfold decodeOrdEdit at hw hlen ⊢
  by_cases h0 : mem a = 0
  · simp only [h0, ↓reduceIte] at hw hlen ⊢
    intro t ht
    interval_cases t <;> (try simp only [Nat.add_zero]) <;> omega
  · simp only [h0, ↓reduceIte] at hw hlen ⊢
    by_cases h12 : mem a = 1 ∨ mem a = 2
    · simp only [h12, ↓reduceIte] at hw hlen ⊢
      obtain ⟨hv, hv', hsel⟩ := hw
      intro t ht
      by_cases ht0 : t = 0
      · subst ht0; simp only [Nat.add_zero]; rcases h12 with h | h <;> omega
      · by_cases ht1 : t = 1
        · subst ht1; omega
        · by_cases ht2 : t = 2
          · subst ht2; omega
          · by_cases ht3 : t = 3
            · subst ht3; omega
            · have hi : t - 4 < mem (a + 3) := by omega
              have hmem : endOfKey (mem (a + t)) ∈
                  ((readList mem (a + 4) (mem (a + 3))).map endOfKey).toFinset := by
                rw [List.mem_toFinset, List.mem_map]
                refine ⟨mem (a + t), ?_, rfl⟩
                unfold readList
                rw [List.mem_map]
                exact ⟨t - 4, List.mem_range.mpr hi, by congr 1; omega⟩
              have he := hsel _ hmem
              unfold endOfKey at he
              omega
    · simp only [h12, ↓reduceIte] at hw hlen ⊢
      by_cases h3 : mem a = 3
      · simp only [h3, ↓reduceIte] at hw hlen ⊢
        obtain ⟨hv, hx, hy⟩ := hw
        intro t ht
        interval_cases t
        · simp only [Nat.add_zero]; omega
        · omega
        · unfold endOfKey at hx; omega
        · by_cases hz : mem (a + 3) = 0
          · omega
          · have hy' := hy (endOfKey (mem (a + 3) - 1)) (by simp [hz])
            unfold endOfKey at hy'; omega
      · simp only [h3, ↓reduceIte] at hw hlen ⊢
        obtain ⟨hv, hy⟩ := hw
        intro t ht
        interval_cases t
        · simp only [Nat.add_zero]; omega
        · omega
        · unfold endOfKey at hy; omega

private theorem decodeOrdEdits_words_lt {mem : ℕ → ℕ} {vCap eCap B : ℕ} :
    ∀ (k a : ℕ), EditsTagsLe4 mem k a →
      OrdEditsWithin vCap eCap (decodeOrdEdits mem k a).1 →
      4 < B → vCap < B → 2 * eCap < B → ((decodeOrdEdits mem k a).2).sum < B →
      ∀ t < ((decodeOrdEdits mem k a).2).sum, mem (a + t) < B
  | 0, _, _, _, _, _, _, _, t, ht => by simp [decodeOrdEdits] at ht
  | k + 1, a, ⟨h0, hrest⟩, hW, h4, hV, hE, hsum, t, ht => by
    simp only [decodeOrdEdits, List.sum_cons] at hsum ht
    have hW1 : OrdEditsWithin vCap eCap [(decodeOrdEdit mem a).1] := fun e he => by
      simp only [List.mem_singleton] at he; subst he
      exact hW _ (by simp [decodeOrdEdits])
    have hW2 : OrdEditsWithin vCap eCap
        (decodeOrdEdits mem k (a + (decodeOrdEdit mem a).2)).1 := fun e he =>
      hW e (by simp [decodeOrdEdits, he])
    by_cases ht1 : t < (decodeOrdEdit mem a).2
    · exact decodeOrdEdit_words_lt h0 hW1 h4 hV hE (by omega) t ht1
    · have ih := decodeOrdEdits_words_lt k (a + (decodeOrdEdit mem a).2) hrest hW2 h4 hV hE
        (by omega) (t - (decodeOrdEdit mem a).2) (by omega)
      rwa [show a + (decodeOrdEdit mem a).2 + (t - (decodeOrdEdit mem a).2) = a + t by omega] at ih

/-- Every word in an `OrdEditsAt` buffer whose tags are `≤ 4` and whose edits lie within
`(vCap, eCap)` is strictly below `B` whenever `4, vCap, 2 * eCap, words < B`. -/
theorem ordEditsAt_words_lt {mem : ℕ → ℕ} {a vCap eCap B words : ℕ} {edits : List OrdEdit}
    (hAt : OrdEditsAt mem a edits words) (htags : EditsTagsLe4 mem edits.length (a + 1))
    (hW : OrdEditsWithin vCap eCap edits)
    (h4 : 4 < B) (hV : vCap < B) (hE : 2 * eCap < B) (hwd : words < B) :
    ∀ t < words, mem (a + t) < B := by
  obtain ⟨hread, hwords, -⟩ := hAt
  have hlen : mem a = edits.length := by
    have := congrArg List.length hread
    unfold readOrdEdits at this
    have hdl : ∀ n p, (decodeOrdEdits mem n p).1.length = n := by
      intro n; induction n with
      | zero => intro _; rfl
      | succ n ih => intro p; simp [decodeOrdEdits, ih]
    rw [hdl] at this; exact this
  intro t ht
  by_cases ht0 : t = 0
  · subst ht0
    have hge : 2 * edits.length ≤ ((decodeOrdEdits mem edits.length (a + 1)).2).sum := by
      clear hread htags hW h4 hV hE hwd hwords hlen ht
      generalize a + 1 = p
      induction edits.length generalizing p with
      | zero => simp [decodeOrdEdits]
      | succ n ih =>
        have h2 := decodeOrdEdit_words_ge_two mem p
        have := ih (p + (decodeOrdEdit mem p).2)
        simp only [decodeOrdEdits, List.sum_cons]
        omega
    rw [Nat.add_zero, hlen]; rw [hlen] at hwords; omega
  · rw [hlen] at hwords
    have hW' : OrdEditsWithin vCap eCap (decodeOrdEdits mem edits.length (a + 1)).1 := by
      unfold readOrdEdits at hread; rw [hlen] at hread; rwa [hread]
    have hlt := decodeOrdEdits_words_lt edits.length (a + 1) htags hW' h4 hV hE (by omega)
      (t - 1) (by omega)
    rwa [show a + 1 + (t - 1) = a + t by omega] at hlt

/-! ## Reading each kind of edit record -/

theorem decodeOrdEdit_drop {mem : ℕ → ℕ} {a e : ℕ} (h0 : mem a = 0) (h1 : mem (a + 1) = e) :
    decodeOrdEdit mem a = (.dropEdge e, 2) := by
  simp [decodeOrdEdit, h0, h1]

theorem decodeOrdEdit_move {mem : ℕ → ℕ} {a tag v v' : ℕ} {keys : List ℕ}
    (htag : tag = 1 ∨ tag = 2) (h0 : mem a = tag) (h1 : mem (a + 1) = v) (h2 : mem (a + 2) = v')
    (h3 : mem (a + 3) = keys.length) (hk : ListAt mem (a + 4) keys) :
    decodeOrdEdit mem a =
      (.moveEnds v v' (keys.map endOfKey).toFinset (decide (tag = 2)), 4 + keys.length) := by
  have hl : readList mem (a + 4) keys.length = keys := by
    unfold readList
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    exact hk i h₂
  have hne : tag ≠ 0 := by omega
  have hne3 : ¬ tag = 3 := by omega
  simp only [decodeOrdEdit, h0, h1, h2, h3, hl, hne, htag, ite_false, ite_true]

theorem decodeOrdEdit_insert {mem : ℕ → ℕ} {a v k y : ℕ} (h0 : mem a = 3) (h1 : mem (a + 1) = v)
    (h2 : mem (a + 2) = k) (h3 : mem (a + 3) = y) :
    decodeOrdEdit mem a =
      (.insertBefore v (endOfKey k) (if y = 0 then none else some (endOfKey (y - 1))), 4) := by
  simp [decodeOrdEdit, h0, h1, h2, h3]

theorem decodeOrdEdit_rotate {mem : ℕ → ℕ} {a v k : ℕ} (h0 : mem a = 4) (h1 : mem (a + 1) = v)
    (h2 : mem (a + 2) = k) :
    decodeOrdEdit mem a = (.rotateTo v (endOfKey k), 3) := by
  simp [decodeOrdEdit, h0, h1, h2]

/-! ## Batch records -/

/-- **One more batch record.** -/
theorem batchBodyAt_snoc {mem : ℕ → ℕ} :
    ∀ {U : List Update} {a : ℕ} {G : MGraph} {words : ℕ} {u : Update} {len : ℕ},
      BatchBodyAt mem a G U words → UpdateAt mem (a + words) (G.applyBatch U) u len →
      BatchBodyAt mem a G (U ++ [u]) (words + len)
  | [], a, G, words, u, len, hB, hu => by
    rw [BatchBodyAt.eq_1] at hB
    subst hB
    rw [List.nil_append, BatchBodyAt.eq_2]
    exact ⟨len, by omega, by simpa [MGraph.applyBatch] using hu, by rw [BatchBodyAt.eq_1]; omega⟩
  | u' :: U, a, G, words, u, len, hB, hu => by
    rw [BatchBodyAt.eq_2] at hB
    obtain ⟨l, hl, hu', hrest⟩ := hB
    rw [List.cons_append, BatchBodyAt.eq_2]
    refine ⟨l, by omega, hu', ?_⟩
    have h := batchBodyAt_snoc (u := u) (len := len) hrest (by
      rw [show a + l + (words - l) = a + words by omega]
      exact hu)
    rwa [show words - l + len = words + len - l by omega] at h

/-- The encoding size of a batch with one more update. -/
theorem batchEnc_snoc : ∀ (G : MGraph) (U : List Update) (u : Update),
    G.batchEnc (U ++ [u]) = G.batchEnc U + (G.applyBatch U).updateEnc u
  | G, [], u => by simp [MGraph.batchEnc, MGraph.applyBatch]
  | G, u' :: U, u => by
    simp only [List.cons_append, MGraph.batchEnc]
    rw [batchEnc_snoc (G.applyUpdate u') U u]
    simp only [MGraph.applyBatch, List.foldl_cons]
    omega

/-- **The full batch in compact form**: a count word, then the records, with at most five words
per unit of encoding size. -/
theorem smallBatchAt_of_body {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {U : List Update} {words : ℕ}
    (hc : mem a = U.length) (hB : BatchBodyAt mem (a + 1) G U words)
    (hw : words ≤ 5 * G.batchEnc U) : SmallBatchAt mem a G U (1 + words) :=
  ⟨⟨by omega, hc, by simpa using hB⟩, by omega⟩

end MinCostFlow.SparseCore.Program
