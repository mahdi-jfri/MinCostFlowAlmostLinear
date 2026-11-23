module

public import MinCostFlow.DynSpanner.Program.DynSpannerDSDefs

import WordRAM.Tactic

/-!
# A batch that stays in memory reads the same (`AssemblyFirstStepP4Congr`)

The loop of Phase 4 runs one spanner update per task. Between the tasks the memory changes, but
the words of each batch stay the same. This file shows that the batch then reads the same
(`p4DecodeBatch_congr`), so its update precondition `DSUpdatePre` still holds at a later heap
pointer (`p4DSUpdatePre_congr`), and the amortized cost and the space of the update do not change
(`p4AmortCost_eq_of_decode`, `p4OpSpace_eq_of_decode`).

These are copies of private lemmas of `AssemblyFirstSpan.lean`.
-/

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

theorem p4DecodeUpdate_congr {mem mem' : ℕ → ℕ} {a : ℕ} {G : MGraph}
    (hag : ∀ k < (decodeUpdate mem a G).2, mem' (a + k) = mem (a + k)) :
    decodeUpdate mem' a G = decodeUpdate mem a G := by
  have hlen_pos : 0 < (decodeUpdate mem a G).2 := by
    unfold decodeUpdate
    split_ifs <;> dsimp only <;> omega
  have h0 : mem' a = mem a := by simpa using hag 0 hlen_pos
  unfold decodeUpdate at hag ⊢
  by_cases hc0 : mem a = 0
  · have h1 := hag 1 (by simp [hc0])
    have h2 := hag 2 (by simp [hc0])
    have h3 := hag 3 (by simp [hc0])
    simp [hc0, h0, h1, h2, h3]
  · by_cases hc1 : mem a = 1
    · have h1 := hag 1 (by simp [hc1])
      simp [hc1, h0, h1]
    · have hlen_ge : 5 + mem (a + 3) + mem (a + 4) ≤
          (if mem a = 0 then (Update.insert (mem (a + 1)) (mem (a + 2)) (mem (a + 3)), 4)
           else if mem a = 1 then (Update.delete (mem (a + 1)), 2)
           else
             let v := mem (a + 1); let kt := mem (a + 3); let kh := mem (a + 4)
             let Lt := (readList mem (a + 5) kt).toFinset
             let Lh := (readList mem (a + 5 + kt) kh).toFinset
             if mem a = 2 then (Update.split v (mem (a + 2)) Lt Lh, 5 + kt + kh)
             else (Update.split v (mem (a + 2)) ({e ∈ G.E | G.tail e = v} \ Lt)
               ({e ∈ G.E | G.head e = v} \ Lh), 5 + kt + kh)).2 := by
        simp only [hc0, hc1, ↓reduceIte]
        split_ifs <;> dsimp only <;> omega
      have h1 := hag 1 (by omega)
      have h2 := hag 2 (by omega)
      have h3 := hag 3 (by omega)
      have h4 := hag 4 (by omega)
      have hkt : readList mem' (a + 5) (mem (a + 3)) = readList mem (a + 5) (mem (a + 3)) := by
        unfold readList
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        simpa [Nat.add_assoc] using hag (5 + i) (by omega)
      have hkh : readList mem' (a + 5 + mem (a + 3)) (mem (a + 4)) =
          readList mem (a + 5 + mem (a + 3)) (mem (a + 4)) := by
        unfold readList
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        simpa [Nat.add_assoc] using hag (5 + mem (a + 3) + i) (by omega)
      simp only [h0, hc0, hc1, ↓reduceIte, h1, h2, h3, h4, hkt, hkh]

theorem p4DecodeBatchBody_congr {mem mem' : ℕ → ℕ} :
    ∀ (n a : ℕ) (G : MGraph),
      (∀ k < (decodeBatchBody mem n a G).2.sum, mem' (a + k) = mem (a + k)) →
      decodeBatchBody mem' n a G = decodeBatchBody mem n a G
  | 0, _, _, _ => rfl
  | n + 1, a, G, hag => by
    unfold decodeBatchBody at hag ⊢
    simp only [List.sum_cons] at hag
    have hd : decodeUpdate mem' a G = decodeUpdate mem a G :=
      p4DecodeUpdate_congr fun k hk => hag k (by omega)
    rw [hd]
    have hrest : decodeBatchBody mem' n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) =
      decodeBatchBody mem n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) :=
      p4DecodeBatchBody_congr n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) fun k hk => by
          have := hag ((decodeUpdate mem a G).2 + k) (by omega)
          simpa [Nat.add_assoc] using this
    dsimp only
    rw [hrest]

theorem p4DecodeBatch_congr {mem mem' : ℕ → ℕ} {a W : ℕ} {G : MGraph}
    (hW : W = 1 + (decodeBatch mem a G).2.sum)
    (hag : ∀ k < W, mem' (a + k) = mem (a + k)) :
    decodeBatch mem' a G = decodeBatch mem a G := by
  unfold decodeBatch at hW ⊢
  have h0 : mem' a = mem a := by simpa using hag 0 (by omega)
  rw [h0]
  exact p4DecodeBatchBody_congr (mem a) (a + 1) G fun k hk => by
    have := hag (1 + k) (by omega)
    simpa [Nat.add_assoc] using this

theorem p4BatchBodyLensAt_congr {mem mem' : ℕ → ℕ} :
    ∀ {a : ℕ} {G : MGraph} {U : List Update} {lens : List ℕ},
      BatchBodyLensAt mem a G U lens →
      (∀ k < lens.sum, mem' (a + k) = mem (a + k)) →
      BatchBodyLensAt mem' a G U lens
  | _, _, [], [], h, _ => h
  | _, _, [], _ :: _, h, _ => h
  | _, _, _ :: _, [], h, _ => h
  | a, G, u :: U, len :: lens, ⟨hu, hrest⟩, hag => by
    simp only [List.sum_cons] at hag
    refine ⟨?_, p4BatchBodyLensAt_congr hrest fun k hk => by
      have := hag (len + k) (by omega); simpa [Nat.add_assoc] using this⟩
    rcases u with ⟨e, x, y⟩ | e | ⟨v, v', St, Sh⟩
    · rcases hu with ⟨rfl, hList⟩
      exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
    · rcases hu with ⟨rfl, hList⟩
      exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
    · rcases hu with ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl, hList⟩ |
        ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl, hList⟩
      · exact Or.inl ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl,
          fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
      · exact Or.inr ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl,
          fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩

theorem p4DSUpdatePre_batch_le {P : DSParams} {d : DSHist} {batchPtr W h : ℕ} {mem : ℕ → ℕ}
    (hpre : DSUpdatePre P d [0, batchPtr, W, h] mem) : batchPtr + W ≤ h := by
  obtain ⟨_, _, _, _, heq, _, _, _, hbp, _⟩ := hpre
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨-, rfl, rfl, rfl⟩
  exact hbp

theorem p4DSUpdatePre_congr {P : DSParams} {d : DSHist} {batchPtr W h h' : ℕ}
    {mem mem' : ℕ → ℕ}
    (hpre : DSUpdatePre P d [0, batchPtr, W, h] mem) (hle : h ≤ h')
    (hag : ∀ k < W, mem' (batchPtr + k) = mem (batchPtr + k)) :
    DSUpdatePre P d [0, batchPtr, W, h'] mem' ∧
      decodeBatch mem' batchPtr (d.state P).G = decodeBatch mem batchPtr (d.state P).G := by
  obtain ⟨_, _, _, _, heq, hw16, hbl, hW, hbp, hwd, hbv, hds, hcaps, hspl, hgen, hlen, hq, hok⟩ :=
    hpre
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨-, rfl, rfl, rfl⟩
  simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some] at hbl hW hbv hds hcaps hspl hgen hlen hok
  have hdec := p4DecodeBatch_congr hW hag
  refine ⟨⟨0, batchPtr, W, h', rfl, hw16, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hq, ?_⟩,
    hdec⟩
  · simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec]
    exact p4BatchBodyLensAt_congr hbl fun k hk => by
      have := hag (1 + k) (by omega); simpa [Nat.add_assoc] using this
  · simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec]
    exact hW
  · intro i hi; rw [hag i hi]; exact hwd i hi
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hbv
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hds
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hcaps
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hspl
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hgen
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hlen
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hok

theorem p4AmortCost_eq_of_decode {P : DSParams} {d : DSHist} {b₁ b₂ batchPtr W h₁ h₂ : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hdec : decodeBatch mem₁ batchPtr (d.state P).G = decodeBatch mem₂ batchPtr (d.state P).G) :
    dsUpdateAmortCost P d [b₁, batchPtr, W, h₁] mem₁ =
      dsUpdateAmortCost P d [b₂, batchPtr, W, h₂] mem₂ := by
  simp only [dsUpdateAmortCost, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, hdec]

theorem p4OpSpace_eq_of_decode {P : DSParams} {d : DSHist} {b₁ b₂ batchPtr W h₁ h₂ : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hdec : decodeBatch mem₁ batchPtr (d.state P).G = decodeBatch mem₂ batchPtr (d.state P).G) :
    dsUpdateOpSpace P d [b₁, batchPtr, W, h₁] mem₁ =
      dsUpdateOpSpace P d [b₂, batchPtr, W, h₂] mem₂ := by
  simp only [dsUpdateOpSpace, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, hdec]

end

end MinCostFlow.SparseCore.Program
