module

public import MinCostFlow.ExpanderDecomp.RouteProgBatchLayout

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Batch Chunk-Chain and Combinatorial Lemmas (`RouteProgBatchLemmas`)

Chunk-chain congruence, monotonicity, and append lemmas (`ChunkChainAt.*`) and pure
combinatorial lemmas for `shortPathBlock`, `batchRoutePairs`, and `batchBallLoop`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 5. Chunk-Chain Lemmas -/

lemma ChunkChainAt.congr {mem mem' : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks)
    (hp : ∀ k, pLo ≤ k → k < pHi → mem' k = mem k)
    (hc : ∀ k, cLo ≤ k → k < cHi → mem' k = mem k) :
    ChunkChainAt mem' X pLo pHi cLo cHi head tail chunks := by
  induction chunks generalizing head with
  | nil => exact h
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨rfl, hlo, hhi, hne, hps, hpl, hnx⟩
      refine ⟨rfl, hlo, hhi, hne, hps, ?_, by rw [hc (head + 1) (by omega) (by omega)]; exact hnx⟩
      rw [hc head hlo (by omega)]
      exact hpl.congr hp
    | cons qs rest' =>
      rcases h with ⟨hlo, hhi, hne, hps, hpl, hht, hlt, hrest⟩
      refine ⟨hlo, hhi, hne, hps, ?_, hht, hlt, ?_⟩
      · rw [hc head hlo (by omega)]; exact hpl.congr hp
      · rw [hc (head + 1) (by omega) (by omega)]; exact ih hrest

lemma ChunkChainAt.mono_pHi {mem : ℕ → ℕ} {X : Finset ℕ} {pLo pHi pHi' cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks) (hle : pHi ≤ pHi') :
    ChunkChainAt mem X pLo pHi' cLo cHi head tail chunks := by
  induction chunks generalizing head with
  | nil => exact h
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨rfl, hlo, hhi, hne, hps, hpl, hnx⟩
      exact ⟨rfl, hlo, hhi, hne, hps, hpl.mono_hi hle, hnx⟩
    | cons qs rest' =>
      rcases h with ⟨hlo, hhi, hne, hps, hpl, hht, hlt, hrest⟩
      exact ⟨hlo, hhi, hne, hps, hpl.mono_hi hle, hht, hlt, ih hrest⟩

lemma ChunkChainAt.mono_cHi {mem : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi cHi' head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks) (hle : cHi ≤ cHi') :
    ChunkChainAt mem X pLo pHi cLo cHi' head tail chunks := by
  induction chunks generalizing head with
  | nil => exact h
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨rfl, hlo, hhi, hne, hps, hpl, hnx⟩
      exact ⟨rfl, hlo, by omega, hne, hps, hpl, hnx⟩
    | cons qs rest' =>
      rcases h with ⟨hlo, hhi, hne, hps, hpl, hht, hlt, hrest⟩
      exact ⟨hlo, by omega, hne, hps, hpl, hht, hlt, ih hrest⟩

lemma ChunkChainAt.head_ne_zero {mem : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks) (hne : chunks ≠ []) :
    head ≠ 0 ∧ cLo ≤ tail ∧ tail + 2 ≤ cHi ∧ tail ≠ 0 ∧ mem (tail + 1) = 0 := by
  induction chunks generalizing head with
  | nil => exact absurd rfl hne
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨rfl, hlo, hhi, h0, _, _, hnx⟩
      exact ⟨h0, hlo, hhi, h0, hnx⟩
    | cons qs rest' =>
      rcases h with ⟨_, _, h0, _, _, _, _, hrest⟩
      exact ⟨h0, (ih hrest (List.cons_ne_nil _ _)).2⟩

/-- Appending a freshly allocated 2-word chunk `[spHead, 0]` at `ch = cHi` onto an existing
`ChunkChainAt` in `[cLo, cHi)` (with `pHi ≤ cLo ∨ cHi + 2 ≤ pLo`). -/
lemma ChunkChainAt.append_fresh {mem : ℕ → ℕ} {X : Finset ℕ}
    {pLo pHi cLo cHi head tail ch spHead : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))} {newPs : List ((ℕ × ℕ) × List ℕ)}
    (hch : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks)
    (hnew_ne : newPs ≠ [])
    (hpl_new : PathListAt mem X pLo pHi spHead newPs)
    (hcLo_hi : cLo ≤ cHi) (hch_eq : ch = cHi) (hch_ne : ch ≠ 0)
    (hdisj_pc : DisjRange pLo (pHi - pLo) cLo (cHi + 2 - cLo))
    (hp_le : pLo ≤ pHi) :
    let mem1 := Function.update (Function.update mem ch spHead) (ch + 1) 0
    let mem2 := if head = 0 then mem1 else Function.update mem1 (tail + 1) ch
    let newHead := if head = 0 then ch else head
    ChunkChainAt mem2 X pLo pHi cLo (cHi + 2) newHead ch (chunks ++ [newPs]) := by
  rcases hch_eq.symm with rfl
  dsimp only
  set mem1 := Function.update (Function.update mem cHi spHead) (cHi + 1) 0
  have hmem1_p : ∀ k, pLo ≤ k → k < pHi → mem1 k = mem k := fun k hk1 hk2 => by
    simp only [mem1,
      Function.update_of_ne (by rcases hdisj_pc with x | x <;> omega : k ≠ cHi + 1),
      Function.update_of_ne (by rcases hdisj_pc with x | x <;> omega : k ≠ cHi)]
  have hmem1_c : ∀ k, cLo ≤ k → k < cHi → mem1 k = mem k := fun k hk1 hk2 => by
    simp only [mem1, Function.update_of_ne (by omega : k ≠ cHi + 1),
      Function.update_of_ne (by omega : k ≠ cHi)]
  cases chunks with
  | nil =>
    rcases hch with ⟨rfl, rfl⟩
    simp only [↓reduceIte, List.nil_append, ChunkChainAt]
    refine ⟨trivial, hcLo_hi, le_rfl, hch_ne, hnew_ne, ?_, by simp [mem1]⟩
    simp only [mem1, Function.update_of_ne (by omega : cHi ≠ cHi + 1), Function.update_self]
    exact hpl_new.congr hmem1_p
  | cons ps rest =>
    have hhead_info := hch.head_ne_zero (List.cons_ne_nil _ _)
    have hhead_ne : head ≠ 0 := hhead_info.1
    have htail_lo : cLo ≤ tail := hhead_info.2.1
    have htail_hi : tail + 2 ≤ cHi := hhead_info.2.2.1
    simp only [hhead_ne, ↓reduceIte]
    set mem2 := Function.update mem1 (tail + 1) cHi
    have hmem2_p : ∀ k, pLo ≤ k → k < pHi → mem2 k = mem k := fun k hk1 hk2 => by
      rw [show mem2 k = Function.update mem1 (tail + 1) cHi k from rfl,
          Function.update_of_ne (by rcases hdisj_pc with x | x <;> omega)]
      exact hmem1_p k hk1 hk2
    have hpl_new2 : PathListAt mem2 X pLo pHi (mem2 cHi) newPs := by
      have hm : mem2 cHi = spHead := by
        simp only [mem2, mem1, Function.update_of_ne (by omega : cHi ≠ tail + 1),
          Function.update_of_ne (by omega : cHi ≠ cHi + 1), Function.update_self]
      rw [hm]; exact hpl_new.congr hmem2_p
    have hnx_new2 : mem2 (cHi + 1) = 0 := by
      simp only [mem2, mem1, Function.update_of_ne (by omega : cHi + 1 ≠ tail + 1), Function.update_self]
    have hch1 : ChunkChainAt mem1 X pLo pHi cLo cHi head tail (ps :: rest) :=
      hch.congr hmem1_p hmem1_c
    clear hch hhead_info hhead_ne hmem1_p hmem1_c
    induction rest generalizing head ps with
    | nil =>
      rcases hch1 with ⟨rfl, hlo, hhi, h0, hps, hpl, _⟩
      simp only [List.singleton_append, ChunkChainAt]
      refine ⟨hlo, by omega, h0, hps, ?_, by omega, by omega, ?_⟩
      · simp only [mem2, Function.update_of_ne (by omega : head ≠ head + 1)]
        exact hpl.congr (fun k hk1 hk2 => Function.update_of_ne (by rcases hdisj_pc with x | x <;> omega) _ _)
      · simp only [mem2, Function.update_self]
        exact ⟨trivial, hcLo_hi, le_rfl, hch_ne, hnew_ne, hpl_new2, hnx_new2⟩
    | cons qs rest' ih =>
      rcases hch1 with ⟨hlo, hhi, h0, hps, hpl, hht, hlt, hrest⟩
      simp only [List.cons_append, ChunkChainAt]
      refine ⟨hlo, by omega, h0, hps, ?_, by omega, by omega, ?_⟩
      · simp only [mem2, Function.update_of_ne (by omega : head ≠ tail + 1)]
        exact hpl.congr (fun k hk1 hk2 => Function.update_of_ne (by rcases hdisj_pc with x | x <;> omega) _ _)
      · simp only [mem2, Function.update_of_ne (by omega : head + 1 ≠ tail + 1)]
        exact ih qs hrest

lemma ChunkChainAt.chunkAddrs_bounds {mem : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks) :
    ∀ a ∈ chunkAddrs mem head chunks.length, cLo ≤ a ∧ a + 2 ≤ cHi := by
  induction chunks generalizing head with
  | nil => simp [chunkAddrs]
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨_, hlo, hhi, _⟩
      simp [chunkAddrs, hlo, hhi]
    | cons qs rest' =>
      rcases h with ⟨hlo, hhi, _, _, _, _, _, hrest⟩
      intro a ha
      change a ∈ head :: chunkAddrs mem (mem (head + 1)) (qs :: rest').length at ha
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact ⟨hlo, hhi⟩
      · exact ih hrest a ha'

lemma ChunkChainAt.tail_mem_chunkAddrs {mem : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks) (hne : chunks ≠ []) :
    tail ∈ chunkAddrs mem head chunks.length := by
  induction chunks generalizing head with
  | nil => exact absurd rfl hne
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases h with ⟨rfl, _⟩
      simp [chunkAddrs]
    | cons qs rest' =>
      rcases h with ⟨_, _, _, _, _, _, _, hrest⟩
      change tail ∈ head :: chunkAddrs mem (mem (head + 1)) (qs :: rest').length
      exact List.mem_cons_of_mem _ (ih hrest (List.cons_ne_nil _ _))

lemma ChunkChainAt.congr_addrs {mem mem' : ℕ → ℕ} {X : Finset ℕ} {pLo pHi cLo cHi head tail : ℕ}
    {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (h : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks)
    (hp : ∀ k, pLo ≤ k → k < pHi → mem' k = mem k)
    (hc : ∀ a ∈ chunkAddrs mem head chunks.length, mem' a = mem a ∧ mem' (a + 1) = mem (a + 1)) :
    ChunkChainAt mem' X pLo pHi cLo cHi head tail chunks ∧
    chunkAddrs mem' head chunks.length = chunkAddrs mem head chunks.length := by
  induction chunks generalizing head with
  | nil => exact ⟨h, rfl⟩
  | cons ps rest ih =>
    have hhead_eq : mem' head = mem head ∧ mem' (head + 1) = mem (head + 1) :=
      hc head (by simp [chunkAddrs])
    cases rest with
    | nil =>
      rcases h with ⟨rfl, hlo, hhi, hne, hps, hpl, hnx⟩
      refine ⟨⟨rfl, hlo, hhi, hne, hps, ?_, by rw [hhead_eq.2]; exact hnx⟩, by simp [chunkAddrs]⟩
      rw [hhead_eq.1]; exact hpl.congr hp
    | cons qs rest' =>
      rcases h with ⟨hlo, hhi, hne, hps, hpl, hht, hlt, hrest⟩
      have hc' : ∀ a ∈ chunkAddrs mem (mem (head + 1)) (qs :: rest').length,
          mem' a = mem a ∧ mem' (a + 1) = mem (a + 1) := fun a ha =>
        hc a (List.mem_cons_of_mem _ ha)
      obtain ⟨hrest', haddrs'⟩ := ih hrest hc'
      refine ⟨⟨hlo, hhi, hne, hps, ?_, hht, hlt, ?_⟩, ?_⟩
      · rw [hhead_eq.1]; exact hpl.congr hp
      · rw [hhead_eq.2]; exact hrest'
      · change head :: chunkAddrs mem' (mem' (head + 1)) (qs :: rest').length =
          head :: chunkAddrs mem (mem (head + 1)) (qs :: rest').length
        rw [hhead_eq.2, haddrs']

lemma ChunkChainAt.chunkAddrs_append_fresh {mem mem' : ℕ → ℕ} {X : Finset ℕ}
    {pLo pHi cLo cHi head tail : ℕ} {chunks : List (List ((ℕ × ℕ) × List ℕ))}
    (hch : ChunkChainAt mem X pLo pHi cLo cHi head tail chunks)
    (hmem_eq : ∀ a ∈ chunkAddrs mem head chunks.length,
      mem' (a + 1) = if a = tail then cHi else mem (a + 1)) :
    let newHead := if head = 0 then cHi else head
    chunkAddrs mem' newHead (chunks.length + 1) = chunkAddrs mem head chunks.length ++ [cHi] := by
  dsimp only
  induction chunks generalizing head with
  | nil =>
    rcases hch with ⟨rfl, rfl⟩
    simp [chunkAddrs]
  | cons ps rest ih =>
    cases rest with
    | nil =>
      rcases hch with ⟨rfl, _, _, h0, _⟩
      have hm1 : mem' (head + 1) = cHi := by
        simpa [chunkAddrs] using hmem_eq head (by simp [chunkAddrs])
      simp [h0, chunkAddrs, hm1]
    | cons qs rest' =>
      rcases hch with ⟨_, _, h0, _, _, hht, _, hrest⟩
      have hm1 : mem' (head + 1) = mem (head + 1) := by
        have := hmem_eq head (by simp [chunkAddrs])
        simpa [hht] using this
      have hsub := ih hrest (fun a ha => hmem_eq a (List.mem_cons_of_mem _ ha))
      have hne_nx : mem (head + 1) ≠ 0 := (hrest.head_ne_zero (List.cons_ne_nil _ _)).1
      simp only [h0, hne_nx, ↓reduceIte] at hsub ⊢
      change head :: chunkAddrs mem' (mem' (head + 1)) ((qs :: rest').length + 1) =
        head :: (chunkAddrs mem (mem (head + 1)) (qs :: rest').length ++ [cHi])
      rw [hm1, hsub]

/-! ## 6. Pure Combinatorial Lemmas for `shortPathBlock`, `batchRoutePairs`, `batchBallLoop` -/

lemma shortPathBlockLoop_diff_le_cost (adj : ℕ → List (ℕ × ℕ)) (S T : Finset ℕ) (d : ℕ) :
    ∀ (rem : ℕ) (V : Finset ℕ) (acc : List ((ℕ × ℕ) × List ℕ)) (c : ℕ),
      let res := shortPathBlockLoop adj S T d rem V acc c
      (V \ res.remVerts).card + c ≤ res.cost ∧
      res.paths.length ≤ acc.length + (V \ res.remVerts).card := by
  intro rem
  induction rem with
  | zero =>
    intro V acc c
    simp [shortPathBlockLoop]
  | succ rem ih =>
    intro V acc c
    dsimp only [shortPathBlockLoop]
    split_ifs with hhit
    · set bfs := bfsLayers adj V S d T
      set dfs := dfsBlock adj V S T bfs.dist bfs.maxReached
      have hdfs : dfs.used ⊆ V ∧ dfs.used.card ≤ dfs.cost ∧ dfs.paths.length ≤ dfs.used.card :=
        dfsBlock_inv adj V S T bfs.dist bfs.maxReached
      obtain ⟨hsub_rem, _⟩ := shortPathBlockLoop_remVerts_sub adj S T d rem (V \ dfs.used)
        (dfs.paths ++ acc) (c + bfs.cost + 1 + dfs.cost)
      obtain ⟨hd, hp⟩ := ih (V \ dfs.used) (dfs.paths ++ acc) (c + bfs.cost + 1 + dfs.cost)
      set res := shortPathBlockLoop adj S T d rem (V \ dfs.used) (dfs.paths ++ acc)
        (c + bfs.cost + 1 + dfs.cost)
      change ((V \ dfs.used) \ res.remVerts).card + (c + bfs.cost + 1 + dfs.cost) ≤ res.cost at hd
      change res.paths.length ≤ (dfs.paths ++ acc).length + ((V \ dfs.used) \ res.remVerts).card at hp
      have hdiff_le : (V \ res.remVerts).card ≤ ((V \ dfs.used) \ res.remVerts).card + dfs.used.card := by
        have hsub : V \ res.remVerts ⊆ ((V \ dfs.used) \ res.remVerts) ∪ dfs.used := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
          by_cases hu : x ∈ dfs.used
          · exact Or.inr hu
          · exact Or.inl ⟨⟨hx.1, hu⟩, hx.2⟩
        exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have hdiff_ge : ((V \ dfs.used) \ res.remVerts).card + dfs.used.card ≤ (V \ res.remVerts).card := by
        have hdisj : Disjoint ((V \ dfs.used) \ res.remVerts) dfs.used := by
          rw [Finset.disjoint_left]; intro x hx; exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2
        have hsub : ((V \ dfs.used) \ res.remVerts) ∪ dfs.used ⊆ V \ res.remVerts := by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
          rcases hx with ⟨⟨hxV, _⟩, hnr⟩ | hxu
          · exact ⟨hxV, hnr⟩
          · exact ⟨hdfs.1 hxu, fun hmr => (Finset.mem_sdiff.mp (hsub_rem hmr)).2 hxu⟩
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card hsub
      simp only [List.length_append] at hp
      exact ⟨by omega, by omega⟩
    · exact ⟨by simp; omega, by simp⟩

lemma shortPathBlock_diff_card_le_cost (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (d : ℕ) :
    (V \ (shortPathBlock adj V S T d).remVerts).card ≤ (shortPathBlock adj V S T d).cost ∧
    (shortPathBlock adj V S T d).paths.length ≤ (V \ (shortPathBlock adj V S T d).remVerts).card := by
  simpa [shortPathBlock] using shortPathBlockLoop_diff_le_cost adj S T d (d + 1) V [] 0

lemma batchRoutePairs_remVerts_sub (adj : ℕ → List (ℕ × ℕ)) (d : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) :
    ∀ V : Finset ℕ,
      let res := batchRoutePairs adj d pairs V
      res.remVerts ⊆ V ∧
      (V \ res.remVerts).card ≤ res.cost ∧
      res.routedCount ≤ (V \ res.remVerts).card ∧
      res.perPairPaths.length = pairs.length ∧
      res.remPairs.length = pairs.length ∧
      res.routedCount = res.perPairPaths.flatten.length := by
  induction pairs with
  | nil =>
    intro V; simp [batchRoutePairs]
  | cons ab rest ih =>
    intro V
    rcases ab with ⟨A, B⟩
    dsimp only [batchRoutePairs]
    set sp := shortPathBlock adj V A B d
    have hsp_sub : sp.remVerts ⊆ V := (shortPathBlockLoop_remVerts_sub adj A B d (d + 1) V [] 0).1
    have hsp_dc := shortPathBlock_diff_card_le_cost adj V A B d
    change (V \ sp.remVerts).card ≤ sp.cost ∧ sp.paths.length ≤ (V \ sp.remVerts).card at hsp_dc
    obtain ⟨ht_sub, ht_dc, ht_rc, ht_pl, ht_rl, ht_fl⟩ := ih sp.remVerts
    have hsplit : (V \ (batchRoutePairs adj d rest sp.remVerts).remVerts).card =
        (V \ sp.remVerts).card + (sp.remVerts \ (batchRoutePairs adj d rest sp.remVerts).remVerts).card := by
      have hdisj : Disjoint (V \ sp.remVerts) (sp.remVerts \ (batchRoutePairs adj d rest sp.remVerts).remVerts) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx1).2 (Finset.mem_sdiff.mp hx2).1
      have heq : V \ (batchRoutePairs adj d rest sp.remVerts).remVerts =
          (V \ sp.remVerts) ∪ (sp.remVerts \ (batchRoutePairs adj d rest sp.remVerts).remVerts) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro ⟨hxV, hnr⟩
          by_cases hxS : x ∈ sp.remVerts
          · exact Or.inr ⟨hxS, hnr⟩
          · exact Or.inl ⟨hxV, hxS⟩
        · rintro (⟨hxV, hns⟩ | ⟨hxS, hnr⟩)
          · exact ⟨hxV, fun h => hns (ht_sub h)⟩
          · exact ⟨hsp_sub hxS, hnr⟩
      rw [heq, Finset.card_union_of_disjoint hdisj]
    refine ⟨Finset.Subset.trans ht_sub hsp_sub, by omega, by omega, by simp [ht_pl], by simp [ht_rl],
      by simp [ht_fl]⟩

lemma shortPathBlock_paths_endpoints_subset (G : Graph) {X V : Finset ℕ} (hVX : V ⊆ X)
    (A B : Finset ℕ) (hAB : Disjoint A B) (d : ℕ) :
    let sp := shortPathBlock (adjOf G X) V A B d
    (∀ p ∈ sp.paths, p.1.1 ∈ A ∧ p.1.2 ∈ B) ∧
    ((sp.paths.map fun p => p.1.1).toFinset.card = sp.paths.length) ∧
    ((sp.paths.map fun p => p.1.2).toFinset.card = sp.paths.length) ∧
    (A \ (sp.paths.map fun p => p.1.1).toFinset).card + sp.paths.length = A.card := by
  have hsp := shortPathBlock_spec G hVX A B hAB d
  set sp := shortPathBlock (adjOf G X) V A B d
  rcases hsp with ⟨_, _, _, hvalid, hdisj, _, _⟩
  have hnd1 : (sp.paths.map fun p => p.1.1).Nodup := by
    generalize sp.paths = ps at hvalid hdisj ⊢
    clear hvalid
    induction ps with
    | nil => simp
    | cons p rest ih =>
      rw [List.pairwise_cons] at hdisj
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hdisj.2⟩
      intro hm; rw [List.mem_map] at hm; rcases hm with ⟨q, hq, heq⟩
      have hp1 : p.1.1 ∈ (walkVerts G.edges p.1.1 p.2).toFinset :=
        List.mem_toFinset.mpr (mem_walkVerts_start _ _ _)
      have hq1 : p.1.1 ∈ (walkVerts G.edges q.1.1 q.2).toFinset := by
        rw [← heq]; exact List.mem_toFinset.mpr (mem_walkVerts_start _ _ _)
      exact Finset.disjoint_left.mp (hdisj.1 q hq) hp1 hq1
  have hnd2 : (sp.paths.map fun p => p.1.2).Nodup := by
    generalize sp.paths = ps at hvalid hdisj ⊢
    induction ps with
    | nil => simp
    | cons p rest ih =>
      rw [List.pairwise_cons] at hdisj
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun q hq => hvalid q (List.mem_cons_of_mem _ hq)) hdisj.2⟩
      intro hm; rw [List.mem_map] at hm; rcases hm with ⟨q, hq, heq⟩
      have hp2 : p.1.2 ∈ (walkVerts G.edges p.1.1 p.2).toFinset :=
        List.mem_toFinset.mpr (hvalid p List.mem_cons_self).2.2.2.1.1.mem_walkVerts_end
      have hq2 : p.1.2 ∈ (walkVerts G.edges q.1.1 q.2).toFinset := by
        rw [← heq]; exact List.mem_toFinset.mpr (hvalid q (List.mem_cons_of_mem _ hq)).2.2.2.1.1.mem_walkVerts_end
      exact Finset.disjoint_left.mp (hdisj.1 q hq) hp2 hq2
  have hsubA : (sp.paths.map fun p => p.1.1).toFinset ⊆ A := by
    intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
    rcases hx with ⟨q, hq, rfl⟩; exact (Finset.mem_inter.mp (hvalid q hq).1).1
  have hc1 : (sp.paths.map fun p => p.1.1).toFinset.card = sp.paths.length := by
    rw [List.toFinset_card_of_nodup hnd1, List.length_map]
  have hc2 : (sp.paths.map fun p => p.1.2).toFinset.card = sp.paths.length := by
    rw [List.toFinset_card_of_nodup hnd2, List.length_map]
  refine ⟨fun q hq => ⟨(Finset.mem_inter.mp (hvalid q hq).1).1, (Finset.mem_inter.mp (hvalid q hq).2.1).1⟩,
    hc1, hc2, ?_⟩
  have hsd := Finset.card_sdiff_add_card_eq_card hsubA
  omega

lemma batchRoutePairs_valid_and_demand (G : Graph) {X : Finset ℕ} (d : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (hvalid : RouteTerminalPairs X pairs) :
    ∀ V : Finset ℕ, V ⊆ X →
      let res := batchRoutePairs (adjOf G X) d pairs V
      RouteTerminalPairs X res.remPairs ∧
      totalDemand res.remPairs + res.routedCount = totalDemand pairs := by
  induction pairs with
  | nil =>
    intro V _
    simp [batchRoutePairs, RouteTerminalPairs, totalDemand]
  | cons ab rest ih =>
    intro V hVX
    rcases ab with ⟨A, B⟩
    have hAB := hvalid.1 (A, B) List.mem_cons_self
    dsimp only at hAB
    have hrest_v : RouteTerminalPairs X rest :=
      ⟨fun q hq => hvalid.1 q (List.mem_cons_of_mem _ hq), (List.pairwise_cons.mp hvalid.2).2⟩
    dsimp only [batchRoutePairs]
    set sp := shortPathBlock (adjOf G X) V A B d
    have hsp_sub : sp.remVerts ⊆ V := (shortPathBlockLoop_remVerts_sub (adjOf G X) A B d (d + 1) V [] 0).1
    have hsp_ep := shortPathBlock_paths_endpoints_subset G hVX A B hAB.2.2.2 d
    change (∀ p ∈ sp.paths, p.1.1 ∈ A ∧ p.1.2 ∈ B) ∧
      (sp.paths.map fun p => p.1.1).toFinset.card = sp.paths.length ∧
      (sp.paths.map fun p => p.1.2).toFinset.card = sp.paths.length ∧
      (A \ (sp.paths.map fun p => p.1.1).toFinset).card + sp.paths.length = A.card at hsp_ep
    obtain ⟨ht_v, ht_d⟩ := ih hrest_v sp.remVerts (Finset.Subset.trans hsp_sub hVX)
    set mL := (sp.paths.map fun p => p.1.1).toFinset
    set mR := (sp.paths.map fun p => p.1.2).toFinset
    have hmR_sub : mR ⊆ B := by
      intro x hx; rw [List.mem_toFinset, List.mem_map] at hx
      rcases hx with ⟨q, hq, rfl⟩; exact (hsp_ep.1 q hq).2
    have hcardB : (B \ mR).card + sp.paths.length = B.card := by
      have := Finset.card_sdiff_add_card_eq_card hmR_sub
      have := hsp_ep.2.2.1; omega
    have hcardA : (A \ mL).card + sp.paths.length = A.card := hsp_ep.2.2.2
    have hAB' : (A \ mL) ⊆ X ∧ (B \ mR) ⊆ X ∧ (A \ mL).card ≤ (B \ mR).card ∧ Disjoint (A \ mL) (B \ mR) :=
      ⟨Finset.Subset.trans Finset.sdiff_subset hAB.1,
       Finset.Subset.trans Finset.sdiff_subset hAB.2.1,
       by have := hAB.2.2.1; omega,
       hAB.2.2.2.mono Finset.sdiff_subset Finset.sdiff_subset⟩
    have hrest_sub_gen : ∀ (rs : List (Finset ℕ × Finset ℕ)) (W : Finset ℕ)
        (q : Finset ℕ × Finset ℕ),
        q ∈ (batchRoutePairs (adjOf G X) d rs W).remPairs →
        ∃ p ∈ rs, q.1 ⊆ p.1 ∧ q.2 ⊆ p.2 := by
      intro rs
      induction rs with
      | nil => intro W q hq; simp [batchRoutePairs] at hq
      | cons p1 r1 ih1 =>
        intro W q hq
        simp only [batchRoutePairs, List.mem_cons] at hq
        rcases hq with rfl | hq'
        · exact ⟨p1, List.mem_cons_self, Finset.sdiff_subset, Finset.sdiff_subset⟩
        · rcases ih1 _ q hq' with ⟨p2, hp2, h1, h2⟩
          exact ⟨p2, List.mem_cons_of_mem _ hp2, h1, h2⟩
    have hrest_sub := hrest_sub_gen rest sp.remVerts
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hAB'
      · exact ht_v.1 q hq'
    · rw [List.pairwise_cons]
      refine ⟨fun q hq => ?_, ht_v.2⟩
      rcases hrest_sub q hq with ⟨p, hp, hq1, hq2⟩
      have hdisj := (List.pairwise_cons.mp hvalid.2).1 p hp
      exact hdisj.mono (Finset.union_subset_union Finset.sdiff_subset Finset.sdiff_subset)
        (Finset.union_subset_union hq1 hq2)
    · simp only [totalDemand, List.map_cons, List.sum_cons] at ht_d ⊢
      omega

/-- Sum of `(A_i \ V_i).card` over a suffix of `pairs` (where `V_i ⊇ V_final`) is bounded by
`(X \ V_final).card` because the `A_i` are pairwise disjoint subsets of `X`. -/
lemma sum_sdiff_le_sdiff_card {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    (hp : RouteTerminalPairs X pairs) (V : Finset ℕ) :
    (pairs.map fun ab => (ab.1 \ V).card).sum ≤ (X \ V).card := by
  induction pairs generalizing X with
  | nil => simp
  | cons ab rest ih =>
    rcases hp with ⟨hmem, hpw⟩
    rw [List.pairwise_cons] at hpw
    have hab := hmem ab List.mem_cons_self
    have hrest : RouteTerminalPairs (X \ ab.1) rest := by
      refine ⟨fun q hq => ?_, hpw.2⟩
      have hq' := hmem q (List.mem_cons_of_mem _ hq)
      have hdisj := hpw.1 q hq
      exact ⟨Finset.subset_sdiff.mpr ⟨hq'.1, (hdisj.mono Finset.subset_union_left Finset.subset_union_left).symm⟩,
        Finset.subset_sdiff.mpr ⟨hq'.2.1, (hdisj.mono Finset.subset_union_left Finset.subset_union_right).symm⟩,
        hq'.2.2.1, hq'.2.2.2⟩
    have hrec := ih hrest
    have heq : (X \ V) = (ab.1 \ V) ∪ ((X \ ab.1) \ V) := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro ⟨hxX, hxnV⟩
        by_cases hxa : x ∈ ab.1
        · exact Or.inl ⟨hxa, hxnV⟩
        · exact Or.inr ⟨⟨hxX, hxa⟩, hxnV⟩
      · rintro (⟨hxa, hxnV⟩ | ⟨⟨hxX, _⟩, hxnV⟩)
        · exact ⟨hab.1 hxa, hxnV⟩
        · exact ⟨hxX, hxnV⟩
    have hdisj_u : Disjoint (ab.1 \ V) ((X \ ab.1) \ V) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx2).1).2 (Finset.mem_sdiff.mp hx1).1
    rw [heq, Finset.card_union_of_disjoint hdisj_u]
    simp only [List.map_cons, List.sum_cons]
    omega

lemma batchBallLoop_cost_add (adj : ℕ → List (ℕ × ℕ)) (X : Finset ℕ) (b h L : ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) :
    ∀ (U Vlive : Finset ℕ) (c1 c2 : ℕ),
      (batchBallLoop adj X b h L pairs U Vlive (c1 + c2)).1 =
        (batchBallLoop adj X b h L pairs U Vlive c1).1 ∧
      (batchBallLoop adj X b h L pairs U Vlive (c1 + c2)).2 =
        (batchBallLoop adj X b h L pairs U Vlive c1).2 + c2 := by
  induction pairs with
  | nil => intro _ _ _ _; exact ⟨rfl, rfl⟩
  | cons ab rest ih =>
    intro U Vlive c1 c2
    rcases ab with ⟨A', B'⟩
    dsimp only [batchBallLoop]
    split_ifs
    · exact ⟨rfl, by omega⟩
    · have : c1 + c2 + 1 = (c1 + 1) + c2 := by omega
      rw [this]; exact ih U Vlive (c1 + 1) c2
    · set br := growBall adj Vlive (A' ∩ Vlive) (B' ∩ Vlive) b h L
      have : c1 + c2 + br.cost + 1 = (c1 + br.cost + 1) + c2 := by omega
      rw [this]; exact ih (U ∪ br.ball) (Vlive \ br.ball) (c1 + br.cost + 1) c2

lemma sort_sdiff_map_locOf {X A M : Finset ℕ} (hAX : A ⊆ X) :
    ((A \ M).sort (· ≤ ·)).map (locOf X) =
      (((A.sort (· ≤ ·)).map (locOf X)).filter fun v => decide (origOf X v ∉ M)) := by
  have h1 : (((A.sort (· ≤ ·)).map (locOf X)).filter fun v => decide (origOf X v ∉ M)) =
      ((A.sort (· ≤ ·)).filter fun u => decide (u ∉ M)).map (locOf X) := by
    have hgen : ∀ l : List ℕ, (∀ u ∈ l, u ∈ X) →
        (l.map (locOf X)).filter (fun v => decide (origOf X v ∉ M)) =
        (l.filter (fun u => decide (u ∉ M))).map (locOf X) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a rest ih =>
        intro hX
        have haX : a ∈ X := hX a List.mem_cons_self
        have hrestX : ∀ u ∈ rest, u ∈ X := fun u hu => hX u (List.mem_cons_of_mem _ hu)
        simp only [List.map_cons, List.filter_cons, origOf_locOf haX]
        rw [ih hrestX]
        by_cases hM : a ∈ M <;> simp [hM]
    exact hgen (A.sort (· ≤ ·)) (fun u hu => hAX ((Finset.mem_sort (· ≤ ·)).mp hu))
  rw [h1]
  congr 1
  have hlt1 : ((A \ M).sort (· ≤ ·)).Pairwise (· < ·) :=
    (((A \ M).pairwise_sort (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp ((A \ M).sort_nodup (· ≤ ·)))).imp
      fun h => Nat.lt_of_le_of_ne h.1 h.2
  have hlt2 : ((A.sort (· ≤ ·)).filter fun u => decide (u ∉ M)).Pairwise (· < ·) := by
    have hA : (A.sort (· ≤ ·)).Pairwise (· < ·) :=
      ((A.pairwise_sort (· ≤ ·)).and (List.nodup_iff_pairwise_ne.mp (A.sort_nodup (· ≤ ·)))).imp
        fun h => Nat.lt_of_le_of_ne h.1 h.2
    exact hA.filter _
  have hnd2 : ((A.sort (· ≤ ·)).filter fun u => decide (u ∉ M)).Nodup :=
    List.nodup_iff_pairwise_ne.mpr (hlt2.imp fun h => Nat.ne_of_lt h)
  have hperm : ((A \ M).sort (· ≤ ·)).Perm ((A.sort (· ≤ ·)).filter fun u => decide (u ∉ M)) := by
    rw [List.perm_ext_iff_of_nodup ((A \ M).sort_nodup (· ≤ ·)) hnd2]
    intro u
    simp [Finset.mem_sort, Finset.mem_sdiff]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (hlt1.imp Nat.le_of_lt) (hlt2.imp Nat.le_of_lt)

lemma growBall_cost_pos (adj : ℕ → List (ℕ × ℕ)) (V S T : Finset ℕ) (b h L : ℕ) :
    1 ≤ (growBall adj V S T b h L).cost := by
  unfold growBall
  dsimp only
  set bfsS := bfsLayers adj V S (h * L) ∅
  set bfsT := bfsLayers adj V T (h * L) ∅
  set sel := if bfsS.visited.card ≤ bfsT.visited.card then bfsS else bfsT
  have h := scanBallLayers_cost_add adj V b sel.layers ∅ 0 0 (bfsS.cost + bfsT.cost + 1)
  simp only [Nat.zero_add] at h
  omega


end MinCostFlow.ExpanderDecomp
