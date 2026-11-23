module

public import WordRAM.Logic
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.PruningBucketProg

/-!
# Initialization of Expander Pruning State in WordRAM

Implements and verifies `initPruneStmt`, building the initial `PruneMemInv` state corresponding
to `initStateList cfg (List.range cfg.G.n).reverse` in `O(n + m + H + 1)` deterministic WordRAM steps:
1. `initSetupRegsStmt`: reads `n, m` from `GraphAt`, sets stack tops to `0`, and computes array pointers.
2. `initZeroVertsStmt`: initializes `outR`, `degX := 0`, `h := 0`, `cur := 0`, `abs := 0`, `ex := 0`,
   `degR := 0`, `inAct := 0`, `lvlNext := n`, `lvlPrev := n` for `u = 0 .. n - 1`.
3. `initZeroLevelsStmt`: initializes `lvlVol[ℓ] := 0`, `lvlHead[ℓ] := n` for `ℓ = 0 .. H`.
4. `initZeroFlowsStmt`: initializes `flowEnc[idx] := C_cap` for `idx = 0 .. m - 1`.
5. `initScanEdgesStmt`: scans `idx = 0 .. m - 1` over `GraphAt` to accumulate exact `degX`,
   `degR`, and `ex` (preserving self-loop degree semantics).
6. `initQueuesStmt`: populates `inAct`, `actStk`, `actTop`, `peelStk`, `peelTop` in forward order
   `u = 0 .. n - 1`, matching `initStateList cfg (List.range cfg.G.n).reverse`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Small Expression / Frame Helpers -/

lemma eval_add_regs_eq {w : ℕ} {st : State} {r₁ r₂ v : ℕ}
    (hsum : st.regs r₁ + st.regs r₂ = v) (hlt : v < 2 ^ w) :
    Expr.eval w st (.bin .add (.reg r₁) (.reg r₂)) = some v := by
  subst hsum
  simp only [Expr.eval, WordRAM.BinOp.eval, hlt, ↓reduceIte]

lemma init_memFrame_weaken {mem mem' : ℕ → ℕ} {lo lo' hi hi' : ℕ}
    (h : MemFrame mem mem' lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    MemFrame mem mem' lo' hi' := by
  intro k hk
  exact h k (by rcases hk with hk1 | hk2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])

lemma init_preservedOutside2_trans {mem mem' mem'' : ℕ → ℕ} {lo1 hi1 lo2 hi2 : ℕ}
    (h1 : PreservedOutside2 mem mem' lo1 hi1 lo2 hi2)
    (h2 : PreservedOutside2 mem' mem'' lo1 hi1 lo2 hi2) :
    PreservedOutside2 mem mem'' lo1 hi1 lo2 hi2 := by
  intro a ha1 ha2
  rw [h2 a ha1 ha2, h1 a ha1 ha2]

lemma init_preservedOutside2_update_left {mem : ℕ → ℕ} {addr v lo1 hi1 lo2 hi2 : ℕ}
    (hlo : lo1 ≤ addr) (hhi : addr < hi1) :
    PreservedOutside2 mem (Function.update mem addr v) lo1 hi1 lo2 hi2 :=
  fun a ha1 _ => Function.update_of_ne (by rcases ha1 with h | h <;> omega) _ _

lemma init_preservedOutside2_update_right {mem : ℕ → ℕ} {addr v lo1 hi1 lo2 hi2 : ℕ}
    (hlo : lo2 ≤ addr) (hhi : addr < hi2) :
    PreservedOutside2 mem (Function.update mem addr v) lo1 hi1 lo2 hi2 :=
  fun a _ ha2 => Function.update_of_ne (by rcases ha2 with h | h <;> omega) _ _

lemma memFrame_to_preserved2_snd {mem mem' : ℕ → ℕ} {lo1 hi1 lo2 hi2 : ℕ}
    (h : MemFrame mem mem' lo2 hi2) :
    PreservedOutside2 mem mem' lo1 hi1 lo2 hi2 :=
  fun a _ ha2 => h a ha2

/-! ## 2. Prefix Combinatorics for Edge Scanning and Reverse Stacks -/

def degXPrefix (G : Cited.Graph) (k u : ℕ) : ℕ :=
  ((G.edges.take k).filter fun e => e.1 = u).length +
  ((G.edges.take k).filter fun e => e.2 = u).length

def degRPrefix (G : Cited.Graph) (inR : ℕ → Bool) (k u : ℕ) : ℕ :=
  if inR u then
    ((G.edges.take k).filter fun e => inR e.1 && inR e.2 && decide (e.1 = u)).length +
    ((G.edges.take k).filter fun e => inR e.1 && inR e.2 && decide (e.2 = u)).length
  else 0

def exPrefix (G : Cited.Graph) (inR : ℕ → Bool) (C k u : ℕ) : ℕ :=
  if inR u then
    C * ((csrIncAux u 0 (G.edges.take k)).filter fun p => !inR p.2.2).length
  else 0

lemma degXPrefix_zero (G : Cited.Graph) (u : ℕ) : degXPrefix G 0 u = 0 := by
  simp [degXPrefix]

lemma degRPrefix_zero (G : Cited.Graph) (inR : ℕ → Bool) (u : ℕ) :
    degRPrefix G inR 0 u = 0 := by
  simp [degRPrefix]

lemma exPrefix_zero (G : Cited.Graph) (inR : ℕ → Bool) (C u : ℕ) :
    exPrefix G inR C 0 u = 0 := by
  simp [exPrefix, csrIncAux]

lemma degXPrefix_succ (G : Cited.Graph) {k : ℕ} (hk : k < G.edges.length) (u : ℕ) :
    let e := G.edges[k]'hk
    degXPrefix G (k + 1) u =
      degXPrefix G k u + (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0) := by
  intro e
  dsimp only [degXPrefix]
  rw [List.take_succ_eq_append_getElem hk, List.filter_append, List.filter_append]
  have hf1 : ([e].filter fun x : ℕ × ℕ => decide (x.1 = u)).length = if e.1 = u then 1 else 0 := by
    by_cases h : e.1 = u <;> simp [h]
  have hf2 : ([e].filter fun x : ℕ × ℕ => decide (x.2 = u)).length = if e.2 = u then 1 else 0 := by
    by_cases h : e.2 = u <;> simp [h]
  rw [List.length_append, List.length_append, hf1, hf2]
  omega

lemma degRPrefix_succ (G : Cited.Graph) (inR : ℕ → Bool) {k : ℕ}
    (hk : k < G.edges.length) (u : ℕ) :
    let e := G.edges[k]'hk
    degRPrefix G inR (k + 1) u =
      if inR e.1 && inR e.2 then
        degRPrefix G inR k u + (if e.1 = u then 1 else 0) + (if e.2 = u then 1 else 0)
      else degRPrefix G inR k u := by
  intro e
  by_cases h12 : inR e.1 = true ∧ inR e.2 = true
  · have hb : (inR e.1 && inR e.2) = true := by simp [h12.1, h12.2]
    simp only [hb, ↓reduceIte, degRPrefix]
    rw [List.take_succ_eq_append_getElem hk]
    by_cases hu : inR u = true
    · simp only [hu, ↓reduceIte]
      have he' : G.edges[k]'hk = e := rfl
      rw [he', List.filter_append, List.filter_append, List.length_append, List.length_append]
      have hf1 : ([e].filter fun x : ℕ × ℕ => inR x.1 && inR x.2 && decide (x.1 = u)).length =
          if e.1 = u then 1 else 0 := by
        rw [List.filter_cons, List.filter_nil]
        by_cases h : e.1 = u <;> simp [h12.1, h12.2, hu, h]
      have hf2 : ([e].filter fun x : ℕ × ℕ => inR x.1 && inR x.2 && decide (x.2 = u)).length =
          if e.2 = u then 1 else 0 := by
        rw [List.filter_cons, List.filter_nil]
        by_cases h : e.2 = u <;> simp [h12.1, h12.2, hu, h]
      rw [hf1, hf2]
      omega
    · have hf : inR u = false := Bool.eq_false_iff.mpr hu
      have hu1 : e.1 ≠ u := fun h => hu (h ▸ h12.1)
      have hu2 : e.2 ≠ u := fun h => hu (h ▸ h12.2)
      simp [hf, hu1, hu2]
  · have hb : (inR e.1 && inR e.2) = false := by
      cases h1 : inR e.1 <;> cases h2 : inR e.2 <;> simp_all
    simp only [hb, Bool.false_eq_true, ↓reduceIte, degRPrefix]
    rw [List.take_succ_eq_append_getElem hk]
    by_cases hu : inR u = true
    · simp only [hu, ↓reduceIte]
      have he' : G.edges[k]'hk = e := rfl
      rw [he', List.filter_append, List.filter_append, List.length_append, List.length_append]
      have hf1 : ([e].filter fun x : ℕ × ℕ => inR x.1 && inR x.2 && decide (x.1 = u)) = [] := by
        rw [List.filter_cons, List.filter_nil]; simp [hb]
      have hf2 : ([e].filter fun x : ℕ × ℕ => inR x.1 && inR x.2 && decide (x.2 = u)) = [] := by
        rw [List.filter_cons, List.filter_nil]; simp [hb]
      rw [hf1, hf2]
      simp
    · have hf : inR u = false := Bool.eq_false_iff.mpr hu
      simp [hf]

lemma exPrefix_succ (G : Cited.Graph) (inR : ℕ → Bool) (C : ℕ) {k : ℕ}
    (hk : k < G.edges.length) (u : ℕ) :
    let e := G.edges[k]'hk
    exPrefix G inR C (k + 1) u =
      if inR e.1 && !inR e.2 then
        exPrefix G inR C k u + if e.1 = u then C else 0
      else if inR e.2 && !inR e.1 then
        exPrefix G inR C k u + if e.2 = u then C else 0
      else exPrefix G inR C k u := by
  intro e
  dsimp only [exPrefix]
  rw [List.take_succ_eq_append_getElem hk, csrIncAux_append_singleton u 0 (G.edges.take k) e.1 e.2]
  by_cases hu : inR u = true
  · simp only [hu, ↓reduceIte, List.filter_append, List.length_append, Nat.mul_add]
    by_cases heq : e.1 = e.2
    · simp [heq]
    · by_cases h12 : inR e.1 = true ∧ inR e.2 = false
      · have hb1 : (inR e.1 && !inR e.2) = true := by simp [h12.1, h12.2]
        simp only [hb1, ↓reduceIte, heq]
        by_cases hu1 : e.1 = u
        · simp [hu1, h12.2]
        · by_cases hu2 : e.2 = u
          · exfalso; rw [hu2] at h12; exact absurd hu (by simp [h12.2])
          · simp [hu1, hu2]
      · have hb1 : (inR e.1 && !inR e.2) = false := by
          cases ha : inR e.1 <;> cases hb : inR e.2 <;> simp_all
        simp only [hb1, Bool.false_eq_true, ↓reduceIte]
        by_cases h21 : inR e.2 = true ∧ inR e.1 = false
        · have hb2 : (inR e.2 && !inR e.1) = true := by simp [h21.1, h21.2]
          simp only [hb2, ↓reduceIte, heq]
          by_cases hu1 : e.1 = u
          · exfalso; rw [hu1] at h21; exact absurd hu (by simp [h21.2])
          · by_cases hu2 : e.2 = u
            · simp [hu1, hu2, h21.2]
            · simp [hu1, hu2]
        · have hb2 : (inR e.2 && !inR e.1) = false := by
            cases ha : inR e.1 <;> cases hb : inR e.2 <;> simp_all
          simp only [hb2, Bool.false_eq_true, ↓reduceIte, heq]
          by_cases ha_u : e.1 = u
          · have : (!inR e.2) = false := by
              have hu_e1 : inR e.1 = true := ha_u ▸ hu
              cases hb : inR e.2 <;> simp_all
            by_cases hb_u : e.2 = u <;> simp_all
          · by_cases hb_u : e.2 = u
            · have : (!inR e.1) = false := by
                have hu_e2 : inR e.2 = true := hb_u ▸ hu
                cases ha : inR e.1 <;> simp_all
              simp [ha_u, hb_u, this]
            · simp [ha_u, hb_u]
  · have hf : inR u = false := Bool.eq_false_iff.mpr hu
    simp only [hf, Bool.false_eq_true, ↓reduceIte]
    split_ifs with h1 h1' h2 h2'
    · exfalso; have h1'' := (Bool.and_eq_true _ _).mp h1; rw [h1'] at h1''; simp [hf] at h1''
    · rfl
    · exfalso; have h2'' := (Bool.and_eq_true _ _).mp h2; rw [h2'] at h2''; simp [hf] at h2''
    · rfl
    · rfl

lemma degXPrefix_le_two_mul_m {G : Cited.Graph} (k u : ℕ) :
    degXPrefix G k u ≤ 2 * G.m := by
  have h1 : ((G.edges.take k).filter fun e : ℕ × ℕ => e.1 = u).length ≤ (G.edges.take k).length :=
    List.length_filter_le _ _
  have h2 : ((G.edges.take k).filter fun e : ℕ × ℕ => e.2 = u).length ≤ (G.edges.take k).length :=
    List.length_filter_le _ _
  have ht : (G.edges.take k).length ≤ G.edges.length := by
    rw [List.length_take]; exact Nat.min_le_right _ _
  dsimp only [degXPrefix, Cited.Graph.m] at *
  omega

lemma degRPrefix_le_two_mul_m {G : Cited.Graph} (inR : ℕ → Bool) (k u : ℕ) :
    degRPrefix G inR k u ≤ 2 * G.m := by
  dsimp only [degRPrefix]
  split_ifs
  · have h1 := List.length_filter_le (fun e : ℕ × ℕ => inR e.1 && inR e.2 && decide (e.1 = u))
      (G.edges.take k)
    have h2 := List.length_filter_le (fun e : ℕ × ℕ => inR e.1 && inR e.2 && decide (e.2 = u))
      (G.edges.take k)
    have ht : (G.edges.take k).length ≤ G.edges.length := by
      rw [List.length_take]; exact Nat.min_le_right _ _
    dsimp only [Cited.Graph.m] at *
    omega
  · exact Nat.zero_le _

lemma exPrefix_le_bound {G : Cited.Graph} (inR : ℕ → Bool) (C k u : ℕ) (hu : u < G.n) :
    exPrefix G inR C k u ≤ 2 * C * G.m := by
  dsimp only [exPrefix]
  split_ifs
  · have hf : ((csrIncAux u 0 (G.edges.take k)).filter fun p => !inR p.2.2).length ≤
        (csrIncAux u 0 (G.edges.take k)).length := List.length_filter_le _ _
    have hc : (csrIncAux u 0 (G.edges.take k)).length ≤ 2 * G.m :=
      csrIncAux_take_length_le_two_mul_m hu k
    calc
      C * ((csrIncAux u 0 (G.edges.take k)).filter fun p => !inR p.2.2).length ≤ C * (2 * G.m) :=
        Nat.mul_le_mul_left _ (le_trans hf hc)
      _ = 2 * C * G.m := by ring
  · exact Nat.zero_le _

lemma degXPrefix_full {cfg : PruneCfg} (hX : cfg.X = Finset.range cfg.G.n)
    (hval : cfg.G.IsValid) (u : ℕ) :
    degXPrefix cfg.G cfg.G.m u = cfg.degX u := by
  dsimp only [degXPrefix, PruneCfg.degX, Cited.Graph.degIn, Cited.Graph.m]
  rw [List.take_length, hX]
  change _ = ((cfg.G.inside cfg.G.verts).filter _).length + ((cfg.G.inside cfg.G.verts).filter _).length
  rw [inside_verts_of_isValid hval]

lemma degRPrefix_full {cfg : PruneCfg} (hX : cfg.X = Finset.range cfg.G.n)
    (hval : cfg.G.IsValid) (inR : ℕ → Bool) (u : ℕ) :
    degRPrefix cfg.G inR cfg.G.m u =
      if inR u then cfg.G.degIn (cfg.X.filter fun x => inR x) u else 0 := by
  dsimp only [degRPrefix]
  split_ifs with hu
  · dsimp only [Cited.Graph.degIn, Cited.Graph.inside, Cited.Graph.m]
    rw [List.take_length, hX]
    have hinside : cfg.G.edges.filter (fun e =>
        decide (e.1 ∈ (Finset.range cfg.G.n).filter (fun x => inR x = true)) &&
        decide (e.2 ∈ (Finset.range cfg.G.n).filter (fun x => inR x = true))) =
        cfg.G.edges.filter (fun e => inR e.1 && inR e.2) := by
      apply List.filter_congr
      intro e he
      have h12 := hval e he
      simp [h12.1, h12.2]
    rw [hinside, List.filter_filter, List.filter_filter]
    congr 1
    · congr 1; apply List.filter_congr; intro e _; simp [Bool.and_comm]
    · congr 1; apply List.filter_congr; intro e _; simp [Bool.and_comm]
  · rfl

lemma filter_range_reverse_getD (n : ℕ) (p : ℕ → Bool) (i : ℕ)
    (hi : i < ((List.range n).filter p).length) :
    (((List.range n).reverse.filter p).getD
      (((List.range n).reverse.filter p).length - 1 - i) 0) =
      ((List.range n).filter p).getD i 0 := by
  have hrev : (List.range n).reverse.filter p = ((List.range n).filter p).reverse := by
    rw [List.filter_reverse]
  rw [hrev, List.length_reverse]
  set L := (List.range n).filter p
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_reverse (by omega)]
  have hidx : L.length - 1 - (L.length - 1 - i) = i := by omega
  rw [hidx]

lemma filter_range_succ (n : ℕ) (p : ℕ → Bool) :
    (List.range (n + 1)).filter p =
      (List.range n).filter p ++ if p n then [n] else [] := by
  rw [List.range_succ, List.filter_append]
  cases hn : p n <;> simp [hn]

/-! ## 3. WordRAM Initialization Statement Pieces -/

/-- Stage 1: loads `n, m`, sets stack tops to `0`, and computes array base pointers. -/
def initSetupRegsStmt : Stmt :=
  seqStmts [
    .assign prN (.load (.reg prG)),
    .assign prM (.load (.bin .add (.reg prG) (.const 1))),
    .assign prActTop (.const 0),
    .assign prPeelTop (.const 0),
    .assign prDegX (.reg prWork),
    .assign prHArr (.bin .add (.reg prDegX) (.reg prN)),
    .assign prCur (.bin .add (.reg prHArr) (.reg prN)),
    .assign prAbs (.bin .add (.reg prCur) (.reg prN)),
    .assign prEx (.bin .add (.reg prAbs) (.reg prN)),
    .assign prDegR (.bin .add (.reg prEx) (.reg prN)),
    .assign prInAct (.bin .add (.reg prDegR) (.reg prN)),
    .assign prActStk (.bin .add (.reg prInAct) (.reg prN)),
    .assign prPeelStk (.bin .add (.reg prActStk) (.reg prN)),
    .assign prLvlNext (.bin .add (.reg prPeelStk) (.reg prN)),
    .assign prLvlPrev (.bin .add (.reg prLvlNext) (.reg prN)),
    .assign prRemArr (.bin .add (.reg prLvlPrev) (.reg prN)),
    .assign prFlowEnc (.bin .add (.reg prRemArr) (.reg prN)),
    .assign prLvlVol (.bin .add (.reg prFlowEnc) (.reg prM)),
    .assign prLvlHead (.bin .add (.reg prLvlVol) (.bin .add (.reg prH) (.const 1))),
    .assign prCsrAdjV (.bin .add (.bin .add (.reg prCsr) (.bin .mul (.const 2) (.reg prN))) (.const 1)),
    .assign prCsrAdjH (.bin .add (.reg prCsrAdjV) (.bin .mul (.const 2) (.reg prM)))
  ]

/-- Stage 2: zeroes vertex arrays `degX, h, cur, abs, ex, degR, inAct`, sets
`lvlNext[u] = lvlPrev[u] = n`, and sets `outR[u] = (inB[u] == 0)` for `u < n`. -/
def initZeroVertsStmt : Stmt :=
  seqStmts [
    .assign prU (.const 0),
    .loop (.bin .lt (.reg prU) (.reg prN))
      (seqStmts [
        .assign prTmp1 (.load (.bin .add (.reg prInB) (.reg prU))),
        .cond (.bin .lt (.const 0) (.reg prTmp1))
          (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 0))
          (.store (.bin .add (.reg prOutR) (.reg prU)) (.const 1)),
        .store (.bin .add (.reg prDegX) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prHArr) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prCur) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prAbs) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prEx) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prDegR) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prInAct) (.reg prU)) (.const 0),
        .store (.bin .add (.reg prLvlNext) (.reg prU)) (.reg prN),
        .store (.bin .add (.reg prLvlPrev) (.reg prU)) (.reg prN),
        .assign prU (.bin .add (.reg prU) (.const 1))
      ])
  ]

/-- Stage 3: sets `lvlVol[ℓ] := 0` and `lvlHead[ℓ] := n` for `ℓ = 0 .. H`. -/
def initZeroLevelsStmt : Stmt :=
  seqStmts [
    .assign prI (.const 0),
    .assign prTmp1 (.bin .add (.reg prH) (.const 1)),
    .loop (.bin .lt (.reg prI) (.reg prTmp1))
      (seqStmts [
        .store (.bin .add (.reg prLvlVol) (.reg prI)) (.const 0),
        .store (.bin .add (.reg prLvlHead) (.reg prI)) (.reg prN),
        .assign prI (.bin .add (.reg prI) (.const 1))
      ])
  ]

/-- Stage 4: sets `flowEnc[idx] := C_cap` for `idx = 0 .. m - 1`. -/
def initZeroFlowsStmt : Stmt :=
  seqStmts [
    .assign prI (.const 0),
    .loop (.bin .lt (.reg prI) (.reg prM))
      (seqStmts [
        .store (.bin .add (.reg prFlowEnc) (.reg prI)) (.reg prCcap),
        .assign prI (.bin .add (.reg prI) (.const 1))
      ])
  ]

/-- Inner conditional updates for one edge `(a, b)` in `prU, prW` with `inR a, inR b` in `prTmp1, prTmp2`. -/
def initScanOneEdgeCondStmt : Stmt :=
  .cond (.bin .lt (.const 0) (.reg prTmp1))
    (.cond (.bin .lt (.const 0) (.reg prTmp2))
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prDegR) (.reg prU)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
        .assign prTmp3 (.bin .add (.reg prDegR) (.reg prW)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1))
      ])
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prEx) (.reg prU)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.reg prCcap))
      ]))
    (.cond (.bin .lt (.const 0) (.reg prTmp2))
      (seqStmts [
        .assign prTmp3 (.bin .add (.reg prEx) (.reg prW)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.reg prCcap))
      ])
      .nop)

/-- Stage 5: scans all `idx < m` over `GraphAt` to accumulate `degX`, `degR`, and `ex`. -/
def initScanEdgesStmt : Stmt :=
  seqStmts [
    .assign prI (.const 0),
    .loop (.bin .lt (.reg prI) (.reg prM))
      (seqStmts [
        .assign prIdx (.bin .add (.bin .add (.reg prG) (.const 2)) (.bin .mul (.const 2) (.reg prI))),
        .assign prU (.load (.reg prIdx)),
        .assign prW (.load (.bin .add (.reg prIdx) (.const 1))),
        .assign prTmp3 (.bin .add (.reg prDegX) (.reg prU)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
        .assign prTmp3 (.bin .add (.reg prDegX) (.reg prW)),
        .store (.reg prTmp3) (.bin .add (.load (.reg prTmp3)) (.const 1)),
        .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
        .assign prTmp2 (.load (.bin .add (.reg prOutR) (.reg prW))),
        initScanOneEdgeCondStmt,
        .assign prI (.bin .add (.reg prI) (.const 1))
      ])
  ]

/-- Stage 6 inner body for vertex `prU`: conditionally pushes `prU` onto `actStk` and `peelStk`. -/
def initQueueOneVertStmt : Stmt :=
  .cond (.bin .lt (.const 0) (.reg prTmp1))
    (seqStmts [
      .assign prTmp2 (.load (.bin .add (.reg prEx) (.reg prU))),
      .cond (.bin .lt (.const 0) (.reg prTmp2))
        (seqStmts [
          .store (.bin .add (.reg prInAct) (.reg prU)) (.const 1),
          .store (.bin .add (.reg prActStk) (.reg prActTop)) (.reg prU),
          .assign prActTop (.bin .add (.reg prActTop) (.const 1))
        ])
        .nop,
      .assign prTmp2 (.load (.bin .add (.reg prDegR) (.reg prU))),
      .cond (.bin .lt (.reg prTmp2) (.reg prTheta))
        (seqStmts [
          .store (.bin .add (.reg prPeelStk) (.reg prPeelTop)) (.reg prU),
          .assign prPeelTop (.bin .add (.reg prPeelTop) (.const 1))
        ])
        .nop
    ])
    .nop

/-- Stage 6: scans `u = 0 .. n - 1` to populate `inAct`, `actStk`, `actTop`, `peelStk`, `peelTop`. -/
def initQueuesStmt : Stmt :=
  seqStmts [
    .assign prU (.const 0),
    .loop (.bin .lt (.reg prU) (.reg prN))
      (seqStmts [
        .assign prTmp1 (.load (.bin .add (.reg prOutR) (.reg prU))),
        initQueueOneVertStmt,
        .assign prU (.bin .add (.reg prU) (.const 1))
      ])
  ]

/-- Full initialization statement establishing `PruneMemInv` for `initStateList cfg (List.range n).reverse`. -/
def initPruneStmt : Stmt :=
  seqStmts [
    initSetupRegsStmt,
    initZeroVertsStmt,
    initZeroLevelsStmt,
    initZeroFlowsStmt,
    initScanEdgesStmt,
    initQueuesStmt
  ]

lemma initSetupRegsStmt_noRand : initSetupRegsStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Stmt.NoRand]

lemma initZeroVertsStmt_noRand : initZeroVertsStmt.NoRand := by
  simp [initZeroVertsStmt, seqStmts, Stmt.NoRand]

lemma initZeroLevelsStmt_noRand : initZeroLevelsStmt.NoRand := by
  simp [initZeroLevelsStmt, seqStmts, Stmt.NoRand]

lemma initZeroFlowsStmt_noRand : initZeroFlowsStmt.NoRand := by
  simp [initZeroFlowsStmt, seqStmts, Stmt.NoRand]

lemma initScanOneEdgeCondStmt_noRand : initScanOneEdgeCondStmt.NoRand := by
  simp [initScanOneEdgeCondStmt, seqStmts, Stmt.NoRand]

lemma initScanEdgesStmt_noRand : initScanEdgesStmt.NoRand := by
  simp [initScanEdgesStmt, seqStmts, Stmt.NoRand, initScanOneEdgeCondStmt_noRand]

lemma initQueueOneVertStmt_noRand : initQueueOneVertStmt.NoRand := by
  simp [initQueueOneVertStmt, seqStmts, Stmt.NoRand]

lemma initQueuesStmt_noRand : initQueuesStmt.NoRand := by
  simp [initQueuesStmt, seqStmts, Stmt.NoRand, initQueueOneVertStmt_noRand]

lemma initPruneStmt_noRand : initPruneStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact initSetupRegsStmt_noRand
  · exact initZeroVertsStmt_noRand
  · exact initZeroLevelsStmt_noRand
  · exact initZeroFlowsStmt_noRand
  · exact initScanEdgesStmt_noRand
  · exact initQueuesStmt_noRand

/-! ## 4. Per-Stage Triple Proofs -/

/-- Entry register configuration before `initPruneStmt` runs. -/
structure InitRegPre (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr : ℕ)
    (st : State) : Prop where
  reg_g : st.regs prG = gAddr
  reg_csr : st.regs prCsr = csrAddr
  reg_inB : st.regs prInB = inBAddr
  reg_outR : st.regs prOutR = outRAddr
  reg_work : st.regs prWork = workAddr
  reg_ccap : st.regs prCcap = cfg.C_cap
  reg_H : st.regs prH = cfg.H
  reg_theta : st.regs prTheta = cfg.θ_out_nat

/-- All setup and layout pointer registers after Stage 1. -/
structure InitPtrRegs (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr : ℕ)
    (st : State) : Prop where
  reg_g : st.regs prG = gAddr
  reg_csr : st.regs prCsr = csrAddr
  reg_inB : st.regs prInB = inBAddr
  reg_outR : st.regs prOutR = outRAddr
  reg_work : st.regs prWork = workAddr
  reg_ccap : st.regs prCcap = cfg.C_cap
  reg_H : st.regs prH = cfg.H
  reg_theta : st.regs prTheta = cfg.θ_out_nat
  reg_n : st.regs prN = cfg.G.n
  reg_m : st.regs prM = cfg.G.m
  reg_actTop : st.regs prActTop = 0
  reg_peelTop : st.regs prPeelTop = 0
  reg_degX : st.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H
  reg_hArr : st.regs prHArr = wHArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_cur : st.regs prCur = wCur workAddr cfg.G.n cfg.G.m cfg.H
  reg_abs : st.regs prAbs = wAbs workAddr cfg.G.n cfg.G.m cfg.H
  reg_ex : st.regs prEx = wEx workAddr cfg.G.n cfg.G.m cfg.H
  reg_degR : st.regs prDegR = wDegR workAddr cfg.G.n cfg.G.m cfg.H
  reg_inAct : st.regs prInAct = wInAct workAddr cfg.G.n cfg.G.m cfg.H
  reg_actStk : st.regs prActStk = wActStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_peelStk : st.regs prPeelStk = wPeelStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlNext : st.regs prLvlNext = wLvlNext workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlPrev : st.regs prLvlPrev = wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H
  reg_remArr : st.regs prRemArr = wRemArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_flowEnc : st.regs prFlowEnc = wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlVol : st.regs prLvlVol = wLvlVol workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlHead : st.regs prLvlHead = wLvlHead workAddr cfg.G.n cfg.G.m cfg.H
  reg_adjV : st.regs prCsrAdjV = csrAddr + 2 * cfg.G.n + 1
  reg_adjH : st.regs prCsrAdjH = csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m

end MinCostFlow.Expander
