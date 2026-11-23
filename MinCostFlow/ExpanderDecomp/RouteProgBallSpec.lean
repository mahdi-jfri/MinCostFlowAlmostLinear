module

public import MinCostFlow.ExpanderDecomp.RouteBall
public import MinCostFlow.ExpanderDecomp.RouteProgBFS
public import MinCostFlow.ExpanderDecomp.RouteProgShortPathBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Ball Growing Word-RAM Procedure: Base Lemmas, Layout, and Sub-Triples

Provides:
1. Pure `adj`-general helper lemmas for `bfsLayers` layer disjointness/nodup, `countIncidence`,
   `addLayerToBall`, `scanBallLayers`, and the unconditional boundary-sum potential `bd ≤ m2`.
2. Configuration block (`BallCfg`, `BallCfgAt`), write set (`BallWriteSet`), disjointness
   (`BallDisj`), output predicate (`BallOutAt`), and deterministic procedure `growBallProc`.
3. Phase-level `BfsDisj` derivations for `S` and `T` and helper sub-triples (`ballLoadCfg_triple`,
   `ballCountInc_triple`, `ballAddLayer_triple`, `ballWriteRet_triple`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.Expander

/-! ## 1. Pure Helper Lemmas for `bfsLayers` Layers and Ball Growing -/

private lemma bfsLoop_layers_inv (adj : ℕ → List (ℕ × ℕ)) (V stopSet : Finset ℕ) :
    ∀ (rem curDist : ℕ) (fr : List ℕ) (revL : List (List ℕ)) (vis : Finset ℕ)
      (dist : ℕ → Option ℕ) (cost : ℕ),
      vis ⊆ V →
      (∀ x ∈ vis, dist x ≠ none) →
      (∀ x, x ∉ vis → dist x = none) →
      revL.reverse.flatten.Nodup →
      (∀ x, x ∈ revL.reverse.flatten ↔ x ∈ vis) →
      let res := bfsLoop adj V stopSet rem curDist fr revL vis dist cost
      res.visited ⊆ V ∧
      res.layers.flatten.Nodup ∧
      (∀ x, x ∈ res.layers.flatten ↔ x ∈ res.visited) ∧
      res.layers.flatten.length = res.visited.card := by
  intro rem
  induction rem with
  | zero =>
    intro curDist fr revL vis dist cost hvisV _ _ hnd hmem
    dsimp only [bfsLoop]
    have hcard : revL.reverse.flatten.length = vis.card := by
      have h1 : revL.reverse.flatten.toFinset = vis := by
        ext x; simp [hmem]
      rw [← h1, List.toFinset_card_of_nodup hnd]
    exact ⟨hvisV, hnd, hmem, hcard⟩
  | succ rem ih =>
    intro curDist fr revL vis dist cost hvisV hdv hdn hnd hmem
    dsimp only [bfsLoop]
    have hex := bfsExpandFrontier_spec adj V (curDist + 1) fr [] vis dist
      hvisV List.nodup_nil (fun _ h => by cases h) hdv hdn (fun _ h => by cases h)
    rcases hex with ⟨_, hsub, hvis'V, hnd_nxt, hmem_nxt, hEq, hNew, hNone, _, _⟩
    set r := bfsExpandFrontier adj V (curDist + 1) fr [] vis dist
    have hmem_nxt' : ∀ x, x ∈ r.1 ↔ x ∈ r.2.1 ∧ x ∉ vis := by
      intro x; simpa using hmem_nxt x
    split_ifs with he hhit
    · have hr1_nil : r.1 = [] := List.isEmpty_iff.mp he
      have hvis_eq : r.2.1 = vis := by
        ext x
        constructor
        · intro hx
          by_contra hx0
          have : x ∈ r.1 := (hmem_nxt' x).mpr ⟨hx, hx0⟩
          rw [hr1_nil] at this; cases this
        · exact fun hx => hsub hx
      have hcard : revL.reverse.flatten.length = r.2.1.card := by
        have h1 : revL.reverse.flatten.toFinset = r.2.1 := by
          ext x; simp [hmem, hvis_eq]
        rw [← h1, List.toFinset_card_of_nodup hnd]
      exact ⟨hvis'V, hnd, fun x => by rw [hvis_eq]; exact hmem x, hcard⟩
    · have hflat : (r.1 :: revL).reverse.flatten = revL.reverse.flatten ++ r.1 := by
        simp [List.reverse_cons, List.flatten_append]
      have hnd' : (r.1 :: revL).reverse.flatten.Nodup := by
        rw [hflat, List.nodup_append]
        refine ⟨hnd, hnd_nxt, fun a ha b hb hab => ?_⟩
        subst hab
        exact ((hmem_nxt' a).mp hb).2 ((hmem a).mp ha)
      have hmem' : ∀ x, x ∈ (r.1 :: revL).reverse.flatten ↔ x ∈ r.2.1 := by
        intro x
        rw [hflat, List.mem_append, hmem x, hmem_nxt' x]
        constructor
        · rintro (h1 | ⟨h2, _⟩); exact hsub h1; exact h2
        · intro hx; by_cases h0 : x ∈ vis; exact Or.inl h0; exact Or.inr ⟨hx, h0⟩
      have hcard : (r.1 :: revL).reverse.flatten.length = r.2.1.card := by
        have h1 : (r.1 :: revL).reverse.flatten.toFinset = r.2.1 := by
          ext x; rw [List.mem_toFinset, hmem']
        rw [← h1, List.toFinset_card_of_nodup hnd']
      exact ⟨hvis'V, hnd', hmem', hcard⟩
    · have hflat : (r.1 :: revL).reverse.flatten = revL.reverse.flatten ++ r.1 := by
        simp [List.reverse_cons, List.flatten_append]
      have hnd' : (r.1 :: revL).reverse.flatten.Nodup := by
        rw [hflat, List.nodup_append]
        refine ⟨hnd, hnd_nxt, fun a ha b hb hab => ?_⟩
        subst hab
        exact ((hmem_nxt' a).mp hb).2 ((hmem a).mp ha)
      have hmem' : ∀ x, x ∈ (r.1 :: revL).reverse.flatten ↔ x ∈ r.2.1 := by
        intro x
        rw [hflat, List.mem_append, hmem x, hmem_nxt' x]
        constructor
        · rintro (h1 | ⟨h2, _⟩); exact hsub h1; exact h2
        · intro hx; by_cases h0 : x ∈ vis; exact Or.inl h0; exact Or.inr ⟨hx, h0⟩
      have hdv' : ∀ x ∈ r.2.1, r.2.2.1 x ≠ none := by
        intro x hx
        by_cases h0 : x ∈ vis
        · rw [hEq x h0]; exact hdv x h0
        · rw [hNew x hx h0]; simp
      exact ih (curDist + 1) r.1 (r.1 :: revL) r.2.1 r.2.2.1
        (cost + r.2.2.2 + 1 + r.1.length) hvis'V hdv' hNone hnd' hmem'

lemma bfsLayers_layers_inv (adj : ℕ → List (ℕ × ℕ)) (V S : Finset ℕ) (maxDist : ℕ)
    (stopSet : Finset ℕ) :
    let res := bfsLayers adj V S maxDist stopSet
    res.visited ⊆ V ∧
    res.layers.flatten.Nodup ∧
    (∀ x, x ∈ res.layers.flatten ↔ x ∈ res.visited) ∧
    res.layers.flatten.length = res.visited.card ∧
    res.layers.length ≤ V.card := by
  have hmain :
      let res := bfsLayers adj V S maxDist stopSet
      res.visited ⊆ V ∧
      res.layers.flatten.Nodup ∧
      (∀ x, x ∈ res.layers.flatten ↔ x ∈ res.visited) ∧
      res.layers.flatten.length = res.visited.card := by
    dsimp only [bfsLayers]
    set S0 := S ∩ V
    set initLayer := S0.sort (· ≤ ·)
    split_ifs with he hhit
    · exact ⟨Finset.empty_subset _, List.nodup_nil, fun _ => by simp, rfl⟩
    · refine ⟨Finset.inter_subset_right,
        by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]; exact S0.sort_nodup (· ≤ ·),
        fun x => by simp [initLayer, Finset.mem_sort], by simp [initLayer, Finset.length_sort]⟩
    · refine bfsLoop_layers_inv adj V stopSet maxDist 0 initLayer [initLayer] S0
        (fun v => if v ∈ S0 then some 0 else none) (initLayer.length + initLayer.length + 1)
        Finset.inter_subset_right (fun x hx => by simp [hx]) (fun x hx => by simp [hx])
        (by simp only [List.reverse_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]; exact S0.sort_nodup (· ≤ ·))
        (fun x => by simp [initLayer, Finset.mem_sort])
  rcases hmain with ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hne := bfsLayers_layers_nonempty adj V S maxDist stopSet
  have hlen_aux : ∀ ls : List (List ℕ), (∀ L ∈ ls, L ≠ []) → ls.length ≤ ls.flatten.length := by
    intro ls
    induction ls with
    | nil => intro _; exact le_rfl
    | cons L rest ih =>
      intro hne'
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      have hLne : L ≠ [] := hne' L List.mem_cons_self
      have hLpos : 1 ≤ L.length := by cases L with | nil => exact absurd rfl hLne | cons _ _ => simp
      have ih' := ih (fun M hM => hne' M (List.mem_cons_of_mem _ hM))
      omega
  have hlen_le := hlen_aux _ hne
  have hcard_le : (bfsLayers adj V S maxDist stopSet).visited.card ≤ V.card := Finset.card_le_card h1
  omega

lemma countIncidence_spec_pub (V cur : Finset ℕ) (u : ℕ) (l : List (ℕ × ℕ)) :
    let r := countIncidence V cur u l
    r.1 = (l.filter fun p => decide (p.1 ∈ cur)).length ∧
    r.2.1 = (l.filter fun p => decide (p.1 ∈ V) && decide (p.1 ∉ insert u cur)).length ∧
    r.2.2 = l.length ∧
    r.1 ≤ l.length ∧ r.2.1 ≤ l.length := by
  induction l with
  | nil => simp [countIncidence]
  | cons p rest ih =>
    rcases p with ⟨w, e⟩
    simp only [countIncidence, List.filter_cons, List.length_cons]
    rcases ih with ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, by omega, ?_, ?_⟩
    · by_cases hw : w ∈ cur <;> simp [hw, h1]
    · by_cases hwV : w ∈ V <;> by_cases hwI : w ∈ insert u cur <;> simp [hwV, hwI, h2]
    · split_ifs <;> omega
    · split_ifs <;> omega

lemma addLayerToBall_cost_add (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) :
    ∀ (L : List ℕ) (cur : Finset ℕ) (bd c1 c2 : ℕ),
      (addLayerToBall adj V L cur bd (c1 + c2)).1 = (addLayerToBall adj V L cur bd c1).1 ∧
      (addLayerToBall adj V L cur bd (c1 + c2)).2.1 = (addLayerToBall adj V L cur bd c1).2.1 ∧
      (addLayerToBall adj V L cur bd (c1 + c2)).2.2 = (addLayerToBall adj V L cur bd c1).2.2 + c2 := by
  intro L
  induction L with
  | nil => intro _ _ _ _; exact ⟨rfl, rfl, rfl⟩
  | cons u rest ih =>
    intro cur bd c1 c2
    dsimp only [addLayerToBall]
    have h1 : c1 + c2 + (countIncidence V cur u (adj u)).2.2 + 1 =
        (c1 + (countIncidence V cur u (adj u)).2.2 + 1) + c2 := by omega
    rw [h1]; exact ih _ _ _ _

lemma scanBallLayers_cost_add (adj : ℕ → List (ℕ × ℕ)) (V : Finset ℕ) (b : ℕ) :
    ∀ (ls : List (List ℕ)) (cur : Finset ℕ) (bd c1 c2 : ℕ),
      (scanBallLayers adj V b ls cur bd (c1 + c2)).1 = (scanBallLayers adj V b ls cur bd c1).1 ∧
      (scanBallLayers adj V b ls cur bd (c1 + c2)).2 = (scanBallLayers adj V b ls cur bd c1).2 + c2 := by
  intro ls
  induction ls with
  | nil => intro _ _ _ _; dsimp only [scanBallLayers]; exact ⟨rfl, by omega⟩
  | cons L rest ih =>
    intro cur bd c1 c2
    dsimp only [scanBallLayers]
    have ha := addLayerToBall_cost_add adj V L cur bd c1 c2
    rw [ha.1, ha.2.1, ha.2.2]
    split_ifs with hstop
    · exact ⟨rfl, by omega⟩
    · have h1 : (addLayerToBall adj V L cur bd c1).2.2 + c2 + 1 =
          ((addLayerToBall adj V L cur bd c1).2.2 + 1) + c2 := by omega
      rw [h1]; exact ih _ _ _ _

lemma bd_pot_step {V cur : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {u bd inCnt outCnt m2 : ℕ}
    (huV : u ∈ V) (hu_not : u ∉ cur)
    (hpot : bd + ∑ v ∈ V \ cur, (adj v).length ≤ m2)
    (hout : outCnt ≤ (adj u).length) :
    bd + outCnt ≤ m2 ∧
    (bd + outCnt - inCnt) + ∑ v ∈ V \ insert u cur, (adj v).length ≤ m2 := by
  have hu_in : u ∈ V \ cur := Finset.mem_sdiff.mpr ⟨huV, hu_not⟩
  have herase : (V \ cur).erase u = V \ insert u cur := by
    ext x; simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]; tauto
  have hsum : (adj u).length + ∑ v ∈ V \ insert u cur, (adj v).length =
      ∑ v ∈ V \ cur, (adj v).length := by
    rw [← herase, Finset.add_sum_erase (V \ cur) (fun v => (adj v).length) hu_in]
  constructor <;> omega

lemma sum_adj_sub_le_m2 {X V : Finset ℕ} {adj : ℕ → List (ℕ × ℕ)} {m2 : ℕ}
    (hVX : V ⊆ X) (hm2 : adjCsrOff X adj X.card ≤ m2) :
    ∑ v ∈ V, (adj v).length ≤ m2 := by
  have h1 : ∑ v ∈ V, (adj v).length ≤ ∑ v ∈ X, (adj v).length :=
    Finset.sum_le_sum_of_subset hVX
  rw [← adjCsrOff_card_eq_sum X adj] at h1
  omega

/-! ## 2. Configuration Block, Write Set, Disjointness, and Statements -/

/-- 18-word input configuration block for `growBallProc` at `cfgAddr + 0 .. cfgAddr + 17`.
Outputs `(ballCnt, outBfsGen, outBallGen)` are written at `cfgAddr + 18 .. cfgAddr + 20`. -/
structure BallCfg where
  bfsCfgAddr : ℕ
  offAddr : ℕ
  nbAddr : ℕ
  maskArrAddr : ℕ
  maskBadVal : ℕ
  layerOffS : ℕ
  layerDataS : ℕ
  layerOffT : ℕ
  layerDataT : ℕ
  sPtr : ℕ
  sLen : ℕ
  tPtr : ℕ
  tLen : ℕ
  ballStampAddr : ℕ
  ballListAddr : ℕ
  bfsGenIn : ℕ
  ballGenIn : ℕ
  b : ℕ

/-- The 18 input configuration words of `cfg` reside at `cfgAddr + 0 .. cfgAddr + 17`. -/
def BallCfgAt (mem : ℕ → ℕ) (cfgAddr : ℕ) (cfg : BallCfg) : Prop :=
  mem (cfgAddr + 0) = cfg.bfsCfgAddr ∧
  mem (cfgAddr + 1) = cfg.offAddr ∧
  mem (cfgAddr + 2) = cfg.nbAddr ∧
  mem (cfgAddr + 3) = cfg.maskArrAddr ∧
  mem (cfgAddr + 4) = cfg.maskBadVal ∧
  mem (cfgAddr + 5) = cfg.layerOffS ∧
  mem (cfgAddr + 6) = cfg.layerDataS ∧
  mem (cfgAddr + 7) = cfg.layerOffT ∧
  mem (cfgAddr + 8) = cfg.layerDataT ∧
  mem (cfgAddr + 9) = cfg.sPtr ∧
  mem (cfgAddr + 10) = cfg.sLen ∧
  mem (cfgAddr + 11) = cfg.tPtr ∧
  mem (cfgAddr + 12) = cfg.tLen ∧
  mem (cfgAddr + 13) = cfg.ballStampAddr ∧
  mem (cfgAddr + 14) = cfg.ballListAddr ∧
  mem (cfgAddr + 15) = cfg.bfsGenIn ∧
  mem (cfgAddr + 16) = cfg.ballGenIn ∧
  mem (cfgAddr + 17) = cfg.b

/-- Addresses that `growBallProc` may overwrite. -/
def BallWriteSet (nX : ℕ) (cfg : BallCfg) (bfsCfg : BfsCfg) (cfgAddr : ℕ) (a : ℕ) : Prop :=
  (bfsCfg.visStampAddr ≤ a ∧ a < bfsCfg.visStampAddr + nX) ∨
  (bfsCfg.distAddr ≤ a ∧ a < bfsCfg.distAddr + nX) ∨
  (bfsCfg.tmpNxtAddr ≤ a ∧ a < bfsCfg.tmpNxtAddr + nX) ∨
  (cfg.layerOffS ≤ a ∧ a < cfg.layerOffS + nX + 1) ∨
  (cfg.layerDataS ≤ a ∧ a < cfg.layerDataS + nX) ∨
  (cfg.layerOffT ≤ a ∧ a < cfg.layerOffT + nX + 1) ∨
  (cfg.layerDataT ≤ a ∧ a < cfg.layerDataT + nX) ∨
  (cfg.bfsCfgAddr + 9 ≤ a ∧ a < cfg.bfsCfgAddr + 21 ∧
    a ≠ cfg.bfsCfgAddr + 11 ∧ a ≠ cfg.bfsCfgAddr + 13) ∨
  (cfg.ballStampAddr ≤ a ∧ a < cfg.ballStampAddr + nX) ∨
  (cfg.ballListAddr ≤ a ∧ a < cfg.ballListAddr + nX) ∨
  (cfgAddr + 18 ≤ a ∧ a < cfgAddr + 21)

/-- Compatibility, disjointness, and word-size bounds for `growBallProc`. -/
structure BallDisj (w nX m2 : ℕ) (cfg : BallCfg) (bfsCfg : BfsCfg) (cfgAddr : ℕ) : Prop where
  bfs_off : bfsCfg.offAddr = cfg.offAddr
  bfs_nb : bfsCfg.nbAddr = cfg.nbAddr
  bfs_mask : bfsCfg.maskArrAddr = cfg.maskArrAddr
  bfs_bad : bfsCfg.maskBadVal = cfg.maskBadVal
  bfs_hasStop : bfsCfg.hasStop = 0
  -- Base BFS disjointness for S and T calls
  bfs_disj_S : BfsDisj w nX m2
    ({ bfsCfg with
        layerOffAddr := cfg.layerOffS
        layerDataAddr := cfg.layerDataS
        bfsGen := cfg.bfsGenIn + 1
        initPtr := cfg.sPtr
        initLen := cfg.sLen }) cfg.bfsCfgAddr
  bfs_disj_T : BfsDisj w nX m2
    ({ bfsCfg with
        layerOffAddr := cfg.layerOffT
        layerDataAddr := cfg.layerDataT
        bfsGen := cfg.bfsGenIn + 2
        initPtr := cfg.tPtr
        initLen := cfg.tLen }) cfg.bfsCfgAddr
  -- S layer buffers preserved during T BFS
  lOffS_bfsT : ∀ a, cfg.layerOffS ≤ a ∧ a < cfg.layerOffS + nX + 1 →
    ¬ BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffT, layerDataAddr := cfg.layerDataT }) cfg.bfsCfgAddr a
  lDataS_bfsT : ∀ a, cfg.layerDataS ≤ a ∧ a < cfg.layerDataS + nX →
    ¬ BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffT, layerDataAddr := cfg.layerDataT }) cfg.bfsCfgAddr a
  lOffS_bcfg : DisjRange cfg.layerOffS (nX + 1) cfg.bfsCfgAddr 21
  lDataS_bcfg : DisjRange cfg.layerDataS nX cfg.bfsCfgAddr 21
  -- ballStamp and ballList pairwise disjoint and disjoint from BFS/read-only/layer buffers
  bs_bl : DisjRange cfg.ballStampAddr nX cfg.ballListAddr nX
  bs_off : DisjRange cfg.ballStampAddr nX cfg.offAddr (nX + 1)
  bs_nb : DisjRange cfg.ballStampAddr nX cfg.nbAddr m2
  bs_mask : DisjRange cfg.ballStampAddr nX cfg.maskArrAddr nX
  bs_lOffS : DisjRange cfg.ballStampAddr nX cfg.layerOffS (nX + 1)
  bs_lDataS : DisjRange cfg.ballStampAddr nX cfg.layerDataS nX
  bs_lOffT : DisjRange cfg.ballStampAddr nX cfg.layerOffT (nX + 1)
  bs_lDataT : DisjRange cfg.ballStampAddr nX cfg.layerDataT nX
  bs_vis : DisjRange cfg.ballStampAddr nX bfsCfg.visStampAddr nX
  bs_bcfg : DisjRange cfg.ballStampAddr nX cfg.bfsCfgAddr 21
  bs_cfg : DisjRange cfg.ballStampAddr nX cfgAddr 21
  bs_bfsS : ∀ a, cfg.ballStampAddr ≤ a ∧ a < cfg.ballStampAddr + nX →
    ¬ BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffS, layerDataAddr := cfg.layerDataS }) cfg.bfsCfgAddr a
  bs_bfsT : ∀ a, cfg.ballStampAddr ≤ a ∧ a < cfg.ballStampAddr + nX →
    ¬ BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffT, layerDataAddr := cfg.layerDataT }) cfg.bfsCfgAddr a
  bl_off : DisjRange cfg.ballListAddr nX cfg.offAddr (nX + 1)
  bl_nb : DisjRange cfg.ballListAddr nX cfg.nbAddr m2
  bl_mask : DisjRange cfg.ballListAddr nX cfg.maskArrAddr nX
  bl_lOffS : DisjRange cfg.ballListAddr nX cfg.layerOffS (nX + 1)
  bl_lDataS : DisjRange cfg.ballListAddr nX cfg.layerDataS nX
  bl_lOffT : DisjRange cfg.ballListAddr nX cfg.layerOffT (nX + 1)
  bl_lDataT : DisjRange cfg.ballListAddr nX cfg.layerDataT nX
  bl_vis : DisjRange cfg.ballListAddr nX bfsCfg.visStampAddr nX
  bl_cfg : DisjRange cfg.ballListAddr nX cfgAddr 21
  -- bfsCfgAddr and cfgAddr disjoint from read-only inputs and visStamp
  bcfg_off : DisjRange cfg.bfsCfgAddr 21 cfg.offAddr (nX + 1)
  bcfg_nb : DisjRange cfg.bfsCfgAddr 21 cfg.nbAddr m2
  bcfg_mask : DisjRange cfg.bfsCfgAddr 21 cfg.maskArrAddr nX
  bcfg_s : DisjRange cfg.bfsCfgAddr 21 cfg.sPtr cfg.sLen
  bcfg_t : DisjRange cfg.bfsCfgAddr 21 cfg.tPtr cfg.tLen
  bcfg_vis : DisjRange cfg.bfsCfgAddr 21 bfsCfg.visStampAddr nX
  bcfg_cfg : DisjRange cfg.bfsCfgAddr 21 cfgAddr 21
  t_bfsS : ∀ a, cfg.tPtr ≤ a ∧ a < cfg.tPtr + cfg.tLen →
    ¬ BfsWriteSet nX ({ bfsCfg with layerOffAddr := cfg.layerOffS, layerDataAddr := cfg.layerDataS }) cfg.bfsCfgAddr a
  cfg_vis : DisjRange cfgAddr 21 bfsCfg.visStampAddr nX
  -- Word-size bounds
  w_cfg : cfgAddr + 24 < 2 ^ w
  w_bs : cfg.ballStampAddr + nX + 5 < 2 ^ w
  w_bl : cfg.ballListAddr + nX + 5 < 2 ^ w
  w_bgen : cfg.bfsGenIn + 5 < 2 ^ w
  w_ballgen : cfg.ballGenIn + 5 < 2 ^ w
  w_mul : 16 * cfg.b * m2 + 5 < 2 ^ w
  w_b16 : 16 * cfg.b + 5 < 2 ^ w

/-- Post-state predicate for `growBallProc` matching `res : BallResult`. -/
def BallOutAt (mem : ℕ → ℕ) (X : Finset ℕ) (cfg : BallCfg) (bfsCfg : BfsCfg)
    (cfgAddr : ℕ) (res : BallResult) : Prop :=
  mem (cfgAddr + 18) = res.ball.card ∧
  mem (cfgAddr + 19) = cfg.bfsGenIn + 2 ∧
  mem (cfgAddr + 20) = cfg.ballGenIn + 1 ∧
  (∃ bl : List ℕ, bl.length = res.ball.card ∧ bl.Nodup ∧
    (∀ x ∈ bl, x < X.card ∧ origOf X x ∈ res.ball) ∧
    (∀ v ∈ res.ball, v ∈ X ∧ locOf X v ∈ bl) ∧
    ListAt mem cfg.ballListAddr bl) ∧
  (∀ v < X.card, mem (cfg.ballStampAddr + v) = cfg.ballGenIn + 1 ↔ origOf X v ∈ res.ball) ∧
  (∀ v < X.card, mem (cfg.ballStampAddr + v) ≤ cfg.ballGenIn + 1) ∧
  (∀ v < X.card, mem (bfsCfg.visStampAddr + v) ≤ cfg.bfsGenIn + 2)

/-- Explicit step bound for `growBallProc` in terms of `res.cost`. -/
def ballProgCost (modelCost : ℕ) : ℕ :=
  150 * modelCost + 750

/-! ## 3. Deterministic Word-RAM Statements for `growBallProc` -/

/-- Load the 18 input words of `BallCfg` into `r1 .. r18`. -/
def ballLoadCfgStmt : Stmt :=
  seqStmts
    [ .assign 1 (.load (.bin .add (.reg 0) (.const 0)))
    , .assign 2 (.load (.bin .add (.reg 0) (.const 1)))
    , .assign 3 (.load (.bin .add (.reg 0) (.const 2)))
    , .assign 4 (.load (.bin .add (.reg 0) (.const 3)))
    , .assign 5 (.load (.bin .add (.reg 0) (.const 4)))
    , .assign 6 (.load (.bin .add (.reg 0) (.const 5)))
    , .assign 7 (.load (.bin .add (.reg 0) (.const 6)))
    , .assign 8 (.load (.bin .add (.reg 0) (.const 7)))
    , .assign 9 (.load (.bin .add (.reg 0) (.const 8)))
    , .assign 10 (.load (.bin .add (.reg 0) (.const 9)))
    , .assign 11 (.load (.bin .add (.reg 0) (.const 10)))
    , .assign 12 (.load (.bin .add (.reg 0) (.const 11)))
    , .assign 13 (.load (.bin .add (.reg 0) (.const 12)))
    , .assign 14 (.load (.bin .add (.reg 0) (.const 13)))
    , .assign 15 (.load (.bin .add (.reg 0) (.const 14)))
    , .assign 16 (.load (.bin .add (.reg 0) (.const 15)))
    , .assign 17 (.load (.bin .add (.reg 0) (.const 16)))
    , .assign 18 (.load (.bin .add (.reg 0) (.const 17))) ]

/-- Count incidences `(r36 = inCnt, r37 = outCnt)` of vertex `r33` over CSR edges `[r34, r35)`. -/
def ballCountIncStmt : Stmt :=
  seqStmts
    [ .assign 36 (.const 0)
    , .assign 37 (.const 0)
    , .loop (.bin .lt (.reg 34) (.reg 35))
        (seqStmts
          [ .assign 38 (.load (.bin .add (.reg 3) (.reg 34)))
          , .cond (.bin .eq (.load (.bin .add (.reg 14) (.reg 38))) (.reg 27))
              (.assign 36 (.bin .add (.reg 36) (.const 1)))
              (.cond (.bin .eq (.reg 38) (.reg 33))
                .nop
                (.cond (.bin .eq (.load (.bin .add (.reg 4) (.reg 38))) (.reg 5))
                  .nop
                  (.assign 37 (.bin .add (.reg 37) (.const 1)))))
          , .assign 34 (.bin .add (.reg 34) (.const 1)) ]) ]

/-- Add all vertices in `selData[r31 .. r32 - 1]` to the ball, updating `r28` (`ballCnt`), `r29` (`bd`),
`ballStamp`, and `ballList`. -/
def ballAddLayerStmt : Stmt :=
  .loop (.bin .lt (.reg 31) (.reg 32))
    (seqStmts
      [ .assign 33 (.load (.bin .add (.reg 25) (.reg 31)))
      , .assign 34 (.load (.bin .add (.reg 2) (.reg 33)))
      , .assign 35 (.load (.bin .add (.reg 2) (.bin .add (.reg 33) (.const 1))))
      , ballCountIncStmt
      , .assign 29 (.bin .sub (.bin .add (.reg 29) (.reg 37)) (.reg 36))
      , .store (.bin .add (.reg 14) (.reg 33)) (.reg 27)
      , .store (.bin .add (.reg 15) (.reg 28)) (.reg 33)
      , .assign 28 (.bin .add (.reg 28) (.const 1))
      , .assign 31 (.bin .add (.reg 31) (.const 1)) ])

/-- Scan complete layers of the selected BFS ball until `16 * b * bd ≤ ballCnt` or layers run out. -/
def ballScanLayersStmt : Stmt :=
  .loop (.reg 26)
    (seqStmts
      [ .assign 31 (.load (.bin .add (.reg 24) (.reg 30)))
      , .assign 32 (.load (.bin .add (.reg 24) (.bin .add (.reg 30) (.const 1))))
      , ballAddLayerStmt
      , .assign 31 (.bin .mul (.bin .mul (.const 16) (.reg 18)) (.reg 29))
      , .cond (.bin .lt (.reg 28) (.reg 31))
          (seqStmts
            [ .assign 30 (.bin .add (.reg 30) (.const 1))
            , .assign 26 (.bin .sub (.reg 26) (.const 1)) ])
          (.assign 26 (.const 0)) ])

/-- Write the 3 output words `(ballCnt, outBfsGen, outBallGen)` and return `ballCnt`. -/
def ballWriteRetStmt : Stmt :=
  seqStmts
    [ .store (.bin .add (.reg 0) (.const 18)) (.reg 28)
    , .store (.bin .add (.reg 0) (.const 19)) (.reg 19)
    , .store (.bin .add (.reg 0) (.const 20)) (.reg 27)
    , .ret (.reg 28) ]

/-- Full deterministic Word-RAM procedure for `growBall` calling BFS `bBfs`. -/
def growBallProc (bBfs : ℕ) : Stmt :=
  seqStmts
    [ ballLoadCfgStmt
    -- BFS from S
    , .assign 19 (.bin .add (.reg 16) (.const 1))
    , .store (.bin .add (.reg 1) (.const 9)) (.reg 6)
    , .store (.bin .add (.reg 1) (.const 10)) (.reg 7)
    , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
    , .store (.bin .add (.reg 1) (.const 14)) (.reg 10)
    , .store (.bin .add (.reg 1) (.const 15)) (.reg 11)
    , .call 20 bBfs [.reg 1]
    , .assign 21 (.load (.bin .add (.reg 1) (.const 16)))
    -- BFS from T
    , .assign 19 (.bin .add (.reg 19) (.const 1))
    , .store (.bin .add (.reg 1) (.const 9)) (.reg 8)
    , .store (.bin .add (.reg 1) (.const 10)) (.reg 9)
    , .store (.bin .add (.reg 1) (.const 12)) (.reg 19)
    , .store (.bin .add (.reg 1) (.const 14)) (.reg 12)
    , .store (.bin .add (.reg 1) (.const 15)) (.reg 13)
    , .call 22 bBfs [.reg 1]
    , .assign 23 (.load (.bin .add (.reg 1) (.const 16)))
    -- Select smaller radius-(h*L) ball
    , .cond (.bin .lt (.reg 22) (.reg 20))
        (seqStmts [ .assign 24 (.reg 8), .assign 25 (.reg 9), .assign 26 (.reg 23) ])
        (seqStmts [ .assign 24 (.reg 6), .assign 25 (.reg 7), .assign 26 (.reg 21) ])
    -- Initialize layer scan
    , .assign 27 (.bin .add (.reg 17) (.const 1))
    , .assign 28 (.const 0)
    , .assign 29 (.const 0)
    , .assign 30 (.const 0)
    , ballScanLayersStmt
    , ballWriteRetStmt ]

theorem growBallProc_noRand (bBfs : ℕ) : (growBallProc bBfs).NoRand := by
  simp [growBallProc, ballLoadCfgStmt, ballCountIncStmt, ballAddLayerStmt,
    ballScanLayersStmt, ballWriteRetStmt, seqStmts, Stmt.NoRand]


end MinCostFlow.ExpanderDecomp
