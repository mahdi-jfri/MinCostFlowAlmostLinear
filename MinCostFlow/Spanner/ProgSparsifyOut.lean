module

public import MinCostFlow.Spanner.ProgKeptEdges
public import MinCostFlow.Spanner.ProgSubgraph
public import MinCostFlow.Spanner.ProgPosTable
public import MinCostFlow.Spanner.ProgMapEmb
public import MinCostFlow.Spanner.ProgComposeEmb

@[expose] public section

/-!
# The Output Stage of `Sparsify`

After Tasks 1, 2 and 3 finish, memory holds the input graph `J`, the witness graph `W`, the
embedding `embWJ` of `W` into `J`, and the embedding `embJW` of `J` into `W`, together with the
path-length bound `γExp`. This file chains the six output procedures (`flatEdges`, `dedupList`,
`subgraph`, `posTable`, `mapEmb`, `composeEmb`) into one fixed procedure `sparsifyOutBody`:

1. Flatten the edges of `embWJ` at `h0` and deduplicate them into `kept` at `pKept + 1`, storing
   `kept.length` at `pKept`.
2. Write the sparsified subgraph `J̃ = subgraphOf J kept` at `pJtilde`.
3. Build the inverse-position table `T` (`T + j ↦ kept.idxOf j`) and rename `embWJ` to
   `embWJtilde` at `E_WJtilde`.
4. Compose `embWJtilde` with `embJW` over `W` to write `embJJtilde = compose W embWJtilde embJW`
   at `pEmb`, leaving `ZeroFrom` at `retHeap`.
5. Store the three output pointers `[pJtilde, pKept, pEmb]` at `[outHdr, outHdr + 3)` and return
   `retHeap`.

The main result is `sparsifyOut_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- Upper bound on heap words allocated above `h0` by `sparsifyOutBody`. -/
def sparsifyOutSpace (mW mJ γExp : ℕ) : ℕ :=
  let L := 2 * γExp + 3
  3 + 3 * (mW * γExp) + 4 * mJ + mW + mW * L + L + 2 * (γExp * L) +
    mJ + mJ * (2 + 2 * (γExp * L))

/-- Upper bound on the step count of `sparsifyOutBody`. -/
def sparsifyOutCost (mW mJ γExp : ℕ) : ℕ :=
  let L := 2 * γExp + 3
  mW * (20 * γExp + 120) + 115 * (mW * γExp) + 90 * mJ +
    mW * (50 * L + 200) + mJ * (γExp * (120 * L + 620) + 300) + 600

/-- Part 1 of the output stage: read `mW`, `mJ`, compute `L`, flatten and deduplicate `embWJ`,
write `kept.length`, build `J̃`, and build the `idxOf` position table `T`. -/
def sparsifyOutPart1 (ff fd fsub fpos : ℕ) : Stmt :=
  .assign 7 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 9 (.bin .add (.bin .add (.reg 4) (.reg 4)) (.const 3)) ;;
  .call 10 ff [.reg 2, .reg 7, .reg 6, .reg 4] ;;
  .assign 11 (.bin .add (.reg 6) (.reg 10)) ;;
  .assign 12 (.bin .add (.reg 11) (.const 1)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 10)) ;;
  .call 14 fd [.reg 6, .reg 10, .reg 8, .reg 12, .reg 13] ;;
  .store (.reg 11) (.reg 14) ;;
  .assign 15 (.bin .add (.bin .add (.reg 13) (.reg 10)) (.reg 8)) ;;
  .call 16 fsub [.reg 0, .reg 12, .reg 14, .reg 15] ;;
  .assign 16 (.bin .add (.bin .add (.reg 15) (.const 2)) (.bin .add (.reg 14) (.reg 14))) ;;
  .call 17 fpos [.reg 12, .reg 14, .reg 16, .reg 8]

/-- Part 2a of the output stage: rename `embWJ` through `T` and compose with `embJW`. -/
def sparsifyOutPart2a (fmap fcomp : ℕ) : Stmt :=
  .assign 17 (.bin .add (.reg 16) (.reg 8)) ;;
  .call 18 fmap [.reg 2, .reg 7, .reg 16, .reg 17, .reg 8, .reg 9] ;;
  .assign 18 (.bin .add (.bin .add (.reg 17) (.reg 7)) (.bin .mul (.reg 7) (.reg 9))) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 9)) ;;
  .assign 20 (.bin .mul (.reg 4) (.reg 9)) ;;
  .assign 21 (.bin .add (.reg 19) (.reg 20)) ;;
  .assign 22 (.bin .add (.reg 21) (.reg 20)) ;;
  .call 23 fcomp [.reg 1, .reg 17, .reg 3, .reg 8, .reg 22, .reg 18, .reg 19, .reg 21, .reg 9,
    .reg 4]

/-- Part 2b of the output stage: compute `retHeap`, write the 3-word output header at `outHdr`,
and return `retHeap`. -/
def sparsifyOutPart2b : Stmt :=
  .assign 23 (.bin .add (.bin .add (.reg 22) (.reg 8))
    (.bin .mul (.reg 8) (.bin .add (.const 2) (.bin .add (.reg 20) (.reg 20))))) ;;
  .store (.reg 5) (.reg 15) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.reg 11) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.reg 22) ;;
  .ret (.reg 23)

/-- Output stage procedure at `args = [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0]`. -/
def sparsifyOutBody (ff fd fsub fpos fmap fcomp : ℕ) : Stmt :=
  sparsifyOutPart1 ff fd fsub fpos ;; sparsifyOutPart2a fmap fcomp ;; sparsifyOutPart2b

theorem sparsifyOutBody_noRand (ff fd fsub fpos fmap fcomp : ℕ) :
    (sparsifyOutBody ff fd fsub fpos fmap fcomp).NoRand := by
  simp [sparsifyOutBody, sparsifyOutPart1, sparsifyOutPart2a, sparsifyOutPart2b, Stmt.NoRand]

/-- Precondition of `sparsifyOutBody`. -/
def SparsifyOutPre (mem : ℕ → ℕ) (jAddr bAddr E_WJ E_JW γExp outHdr h0 : ℕ)
    (J W : Graph) (embWJ embJW : ℕ → Walk) (w : ℕ) : Prop :=
  GraphAt mem jAddr J ∧ GraphAt mem bAddr W ∧
  jAddr + J.encode.length ≤ h0 ∧ bAddr + W.encode.length ≤ h0 ∧
  EmbAt mem E_WJ W.m embWJ ∧ EmbBounded mem E_WJ W.m embWJ h0 ∧
  EmbAt mem E_JW J.m embJW ∧ EmbBounded mem E_JW J.m embJW h0 ∧
  IsEmbedding W J embWJ ∧ IsEmbedding J W embJW ∧
  W.IsValid ∧ J.n < 2 ^ w ∧ W.n = J.n ∧
  (∀ e < W.m, (embWJ e).edges.length ≤ γExp) ∧
  (∀ e < J.m, (embJW e).edges.length ≤ γExp) ∧
  outHdr + 3 ≤ h0 ∧ ZeroFrom mem h0 ∧
  h0 + sparsifyOutSpace W.m J.m γExp < 2 ^ w ∧ 1 < 2 ^ w

/-- Postcondition of `sparsifyOutBody`. -/
def SparsifyOutPost (mem mem' : ℕ → ℕ) (γExp outHdr h0 retHeap : ℕ)
    (J W : Graph) (embWJ embJW : ℕ → Walk) : Prop :=
  let kept := (flatEdges embWJ W.m).dedup
  let Jtilde := subgraphOf J kept
  let embWJtilde : ℕ → Walk := fun eW => (embWJ eW).mapEdges kept.idxOf
  let embJJtilde := compose W embWJtilde embJW
  outHdr + 3 ≤ retHeap ∧ h0 ≤ retHeap ∧ retHeap ≤ h0 + sparsifyOutSpace W.m J.m γExp ∧
  ZeroFrom mem' retHeap ∧
  let pJtilde := mem' outHdr
  let pKept := mem' (outHdr + 1)
  let pEmb := mem' (outHdr + 2)
  h0 ≤ pJtilde ∧ h0 ≤ pKept ∧ h0 ≤ pEmb ∧
  pJtilde + Jtilde.encode.length ≤ retHeap ∧
  pKept + 1 + kept.length ≤ retHeap ∧
  pEmb + J.m ≤ retHeap ∧
  GraphAt mem' pJtilde Jtilde ∧
  ListAt mem' pKept (kept.length :: kept) ∧
  EmbAt mem' pEmb J.m embJJtilde ∧
  EmbBounded mem' pEmb J.m embJJtilde retHeap ∧
  (∀ x < h0, x ≠ outHdr → x ≠ outHdr + 1 → x ≠ outHdr + 2 → mem' x = mem x)

/-- Contract of `sparsifyOutBody`. -/
def sparsifyOutContract (w : ℕ) : Contract where
  pre args mem := ∃ jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW,
    args = [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0] ∧
    SparsifyOutPre mem jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW w
  post args mem v mem' := ∀ jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW,
    args = [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0] →
    SparsifyOutPre mem jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW w →
    SparsifyOutPost mem mem' γExp outHdr h0 v J W embWJ embJW
  cost args mem :=
    sparsifyOutCost (mem (args.getD 1 0 + 1)) (mem (args.getD 0 0 + 1)) (args.getD 4 0)

/-! ### Auxiliary lemmas -/

private lemma dedup_length_le_bound {xs : List ℕ} {bound : ℕ} (h : ∀ x ∈ xs, x < bound) :
    xs.dedup.length ≤ bound := by
  have hsub : xs.dedup.toFinset ⊆ Finset.range bound := by
    intro x hx
    rw [List.mem_toFinset, List.mem_dedup] at hx
    exact Finset.mem_range.mpr (h x hx)
  calc xs.dedup.length = xs.dedup.toFinset.card :=
        (List.toFinset_card_of_nodup (List.nodup_dedup xs)).symm
    _ ≤ (Finset.range bound).card := Finset.card_le_card hsub
    _ = bound := Finset.card_range bound

private lemma listAt_cons_of_head {mem : ℕ → ℕ} {a x : ℕ} {xs : List ℕ}
    (hh : mem a = x) (ht : ListAt mem (a + 1) xs) : ListAt mem a (x :: xs) := by
  intro i hi
  cases i with
  | zero => simpa using hh
  | succ j =>
    have hj : j < xs.length := by simpa using hi
    have h1 := ht j hj
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using h1

private lemma walk_append_encode_le (P Q : Walk) :
    (Walk.encode (P.append Q)).length ≤ (Walk.encode P).length + (Walk.encode Q).length := by
  dsimp only [Walk.append]
  split_ifs
  · omega
  · omega
  · rw [walk_encode_length, walk_encode_length, walk_encode_length]
    simp only [List.length_append, List.length_tail]
    omega

private lemma walk_reverse_encode_length (P : Walk) :
    (Walk.encode P.reverse).length = (Walk.encode P).length := by
  simp [walk_encode_length, Walk.reverse]

private lemma composeAux_encode_le (B : Graph) {embBC : ℕ → Walk} {L : ℕ}
    (hL : ∀ j < B.m, (Walk.encode (embBC j)).length ≤ L) :
    ∀ (vs es : List ℕ), (∀ j ∈ es, j < B.m) →
      (Walk.encode (composeAux B embBC vs es)).length ≤ 2 + 2 * (es.length * L)
  | [], _, _ => by simp [composeAux, Walk.empty, Walk.encode]
  | [_], _, _ => by simp [composeAux, Walk.empty, Walk.encode]
  | _ :: _ :: _, [], _ => by simp [composeAux, Walk.empty, Walk.encode]
  | u :: v :: vs, j :: js, hes => by
    unfold composeAux
    dsimp only
    have hj : j < B.m := hes j List.mem_cons_self
    have hrest := composeAux_encode_le B hL (v :: vs) js
      (fun x hx => hes x (List.mem_cons_of_mem j hx))
    set step := if (B.edges.getD j (0, 0)).1 = u ∧ (B.edges.getD j (0, 0)).2 = v
      then embBC j else (embBC j).reverse
    have hstep : (Walk.encode step).length ≤ L := by
      dsimp only [step]
      split_ifs
      · exact hL j hj
      · rw [walk_reverse_encode_length]; exact hL j hj
    have happ := walk_append_encode_le step (composeAux B embBC (v :: vs) js)
    simp only [List.length_cons, Nat.succ_mul]
    omega

private lemma embOffs_compose_le {B : Graph} {embBC embAB : ℕ → Walk} {m L K : ℕ}
    (hL : ∀ j < B.m, (Walk.encode (embBC j)).length ≤ L)
    (hK : ∀ e < m, (embAB e).edges.length ≤ K)
    (hedg : ∀ e < m, ∀ j ∈ (embAB e).edges, j < B.m) :
    ∀ k ≤ m, embOffs (compose B embBC embAB) k ≤ k * (2 + 2 * (K * L))
  | 0, _ => by simp [embOffs]
  | k + 1, hk => by
    rw [embOffs, Nat.succ_mul]
    have ih := embOffs_compose_le hL hK hedg k (by omega)
    have h1 := composeAux_encode_le B hL (embAB k).verts (embAB k).edges (hedg k (by omega))
    have h2 : (embAB k).edges.length * L ≤ K * L := Nat.mul_le_mul_right L (hK k (by omega))
    have h3 : (Walk.encode (compose B embBC embAB k)).length ≤ 2 + 2 * (K * L) := by
      unfold compose; omega
    omega

private lemma embWJ_trunc_props {W J : Graph} {embWJ : ℕ → Walk} {γExp : ℕ}
    (hEmb : IsEmbedding W J embWJ) (hLen : ∀ e < W.m, (embWJ e).edges.length ≤ γExp) :
    let emb' : ℕ → Walk := fun e => if e < W.m then embWJ e else Walk.empty
    (∀ e < W.m, emb' e = embWJ e) ∧
    (∀ e, (emb' e).edges.length ≤ γExp) ∧
    (∀ e, (Walk.encode (emb' e)).length ≤ 2 * γExp + 3) := by
  intro emb'
  refine ⟨fun e he => by simp [emb', he], fun e => ?_, fun e => ?_⟩
  · dsimp only [emb']
    split_ifs with he
    · exact hLen e he
    · simp [Walk.empty]
  · dsimp only [emb']
    split_ifs with he
    · have hsh := (isEmbedding_walk_facts hEmb he).1
      have hle := hLen e he
      rw [walk_encode_length]
      rcases hsh with h | ⟨hv, he'⟩
      · omega
      · simp [hv, he']
    · simp [Walk.empty, Walk.encode]

/-! ### Part 1 and Part 2 verification -/

/-- State reached after `sparsifyOutPart1` (`flatEdges`, `dedupList`, `subgraph`, `posTable`). -/
private def Part1Post (mem : ℕ → ℕ) (jAddr bAddr E_WJ E_JW γExp outHdr h0 pKept pJtilde T : ℕ)
    (J W : Graph) (embWJ : ℕ → Walk) (st : State) : Prop :=
  let kept := (flatEdges embWJ W.m).dedup
  st.regs 0 = jAddr ∧ st.regs 1 = bAddr ∧ st.regs 2 = E_WJ ∧ st.regs 3 = E_JW ∧
  st.regs 4 = γExp ∧ st.regs 5 = outHdr ∧ st.regs 6 = h0 ∧ st.regs 7 = W.m ∧
  st.regs 8 = J.m ∧ st.regs 9 = 2 * γExp + 3 ∧ st.regs 11 = pKept ∧ st.regs 15 = pJtilde ∧
  st.regs 16 = T ∧
  h0 ≤ pKept ∧ h0 ≤ pJtilde ∧
  pKept + 1 + kept.length ≤ T + J.m ∧
  pJtilde + (2 + 2 * kept.length) ≤ T + J.m ∧
  T ≤ h0 + 3 + 3 * (W.m * γExp) + 3 * J.m ∧
  (∀ x < h0, st.mem x = mem x) ∧
  ListAt st.mem pKept (kept.length :: kept) ∧
  GraphAt st.mem pJtilde (subgraphOf J kept) ∧
  (∀ j ∈ kept, st.mem (T + j) = kept.idxOf j) ∧
  ZeroFrom st.mem (T + J.m)

private lemma sparsifyOut_part1_runs {w : ℕ} {p : Program} {ff fd fsub fpos : ℕ}
    (hff : MeetsContract w p ff (flatEdgesContract w))
    (hfd : MeetsContract w p fd (dedupListContract w))
    (hfsub : MeetsContract w p fsub (subgraphContract w))
    (hfpos : MeetsContract w p fpos (posTableContract w))
    {mem : ℕ → ℕ} {jAddr bAddr E_WJ E_JW γExp outHdr h0 pos : ℕ} {ω : ℕ → Bool}
    {J W : Graph} {embWJ embJW : ℕ → Walk}
    (hwords : ∀ a ∈ [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0], a < 2 ^ w)
    (hpre : SparsifyOutPre mem jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW w) :
    ∃ pKept pJtilde T o st₁ c₁,
      Runs w p ω (sparsifyOutPart1 ff fd fsub fpos)
        (startState [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0] mem pos) o st₁ c₁ ∧
      (o = .normal ∧ Part1Post mem jAddr bAddr E_WJ E_JW γExp outHdr h0 pKept pJtilde T J W embWJ st₁) ∧
      c₁ ≤ W.m * (20 * γExp + 120) + 115 * (W.m * γExp) + 90 * J.m + 250 := by
  obtain ⟨hgJ, hgW, hJh0, hWh0, hEWJ, hBWJ, _, _, hEmbWJ, _, _, _, _, hLenWJ, _,
    hOuth0, hZ0, hSpw, hw1⟩ := hpre
  set L := 2 * γExp + 3 with hLdef
  set emb' : ℕ → Walk := fun e => if e < W.m then embWJ e else Walk.empty
  obtain ⟨hemb'_eq, hemb'_len, _⟩ := embWJ_trunc_props hEmbWJ hLenWJ
  have hEWJ' : EmbAt mem E_WJ W.m emb' := fun e he => by simp only [emb', he, ↓reduceIte]; exact hEWJ e he
  have hBWJ' : EmbBounded mem E_WJ W.m emb' h0 :=
    ⟨hBWJ.1, fun e he => by
      show mem (E_WJ + e) + (Walk.encode (emb' e)).length ≤ h0
      simp only [emb', he, ↓reduceIte]; exact hBWJ.2 e he⟩
  have hflat_eq : flatEdges emb' W.m = flatEdges embWJ W.m := flatEdges_congr hemb'_eq
  set xs := flatEdges embWJ W.m with hxs_def
  set kept := xs.dedup with hkept_def
  have hxs_le : xs.length ≤ W.m * γExp := hflat_eq ▸ flatEdges_length_le hemb'_len W.m
  have hxs_lt_J : ∀ x ∈ xs, x < J.m := fun x hx => by
    obtain ⟨e, he, hxe⟩ := mem_flatEdges hx
    exact (isEmbedding_walk_facts hEmbWJ he).2.2 x hxe
  have hkept_lt : ∀ j ∈ kept, j < J.m := fun j hj => hxs_lt_J j (List.mem_dedup.mp hj)
  have hkept_le : kept.length ≤ J.m := dedup_length_le_bound hxs_lt_J
  have hkept_le_xs : kept.length ≤ xs.length := (List.dedup_sublist xs).length_le
  have hsp_exp : sparsifyOutSpace W.m J.m γExp =
      3 + 3 * (W.m * γExp) + 4 * J.m + W.m + W.m * L + L + 2 * (γExp * L) +
        J.m + J.m * (2 + 2 * (γExp * L)) := rfl
  have hwJ : jAddr < 2 ^ w := hwords jAddr (by simp)
  have hwB : bAddr < 2 ^ w := hwords bAddr (by simp)
  have hwEWJ : E_WJ < 2 ^ w := hwords E_WJ (by simp)
  have hwEJW : E_JW < 2 ^ w := hwords E_JW (by simp)
  have hwG : γExp < 2 ^ w := hwords γExp (by simp)
  have hwOut : outHdr < 2 ^ w := hwords outHdr (by simp)
  have hwH0 : h0 < 2 ^ w := hwords h0 (by simp)
  have hmW_val : mem (bAddr + 1) = W.m := by simpa [GraphAt, Graph.encode] using hgW 1 (by simp [Graph.encode])
  have hmJ_val : mem (jAddr + 1) = J.m := by simpa [GraphAt, Graph.encode] using hgJ 1 (by simp [Graph.encode])
  have hJl : J.encode.length = 2 + 2 * J.m := graph_encode_length J
  have hWl : W.encode.length = 2 + 2 * W.m := graph_encode_length W
  let s0 := startState [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0] mem pos
  have e7 : (Expr.load (.bin .add (.reg 1) (.const 1))).eval w s0 = some W.m :=
    ev_load' (ev_add (ev_reg (by simp [s0, startState]) hwB) (ev_const hw1) (by omega)) hmW_val
  let s1 : State := { s0 with regs := Function.update s0.regs 7 W.m }
  have e8 : (Expr.load (.bin .add (.reg 0) (.const 1))).eval w s1 = some J.m :=
    ev_load' (ev_add (ev_reg (by simp [s1, s0, startState]) hwJ) (ev_const hw1) (by omega)) hmJ_val
  let s2 : State := { s1 with regs := Function.update s1.regs 8 J.m }
  have e9 : (Expr.bin .add (.bin .add (.reg 4) (.reg 4)) (.const 3)).eval w s2 = some L := by
    have h4 : (Expr.reg 4).eval w s2 = some γExp := ev_reg (by simp [s2, s1, s0, startState]) hwG
    have ha := ev_add h4 h4 (by omega)
    have hb := ev_add ha (ev_const (by omega : 3 < 2 ^ w)) (by omega)
    simpa [L, two_mul] using hb
  let s3 : State := { s2 with regs := Function.update s2.regs 9 L }
  have hFPre : FlatEdgesPre mem E_WJ W.m h0 γExp emb' w :=
    ⟨hEWJ', hBWJ', hemb'_len, by omega, hw1⟩
  set pKept := h0 + xs.length with hpKept_def
  set kAddr := pKept + 1 with hkAddr_def
  set dedupH := kAddr + xs.length with hdedupH_def
  set pJtilde := dedupH + xs.length + J.m with hpJtilde_def
  set T := pJtilde + 2 + 2 * kept.length with hT_def
  refine ⟨pKept, pJtilde, T, ?_⟩
  unfold sparsifyOutPart1
  refine runs_start_le ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_assign_le e8 ?_
  refine runs_seq_assign_le e9 ?_
  refine runs_seq_call_le (vs := [E_WJ, W.m, h0, γExp]) hff
    (by simp [evalArgs, Expr.eval, startState])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega)
    ⟨E_WJ, W.m, h0, γExp, emb', rfl, hFPre⟩ ?_
  intro v1 mem1 pos1 hpost1
  obtain ⟨hv1, hlist1, hout1⟩ := hpost1 E_WJ W.m h0 γExp emb' rfl hFPre
  rw [hflat_eq] at hv1 hlist1 hout1
  let s4 : State := { mem := mem1, regs := Function.update s3.regs 10 v1, pos := pos1 }
  have e11 : (Expr.bin .add (.reg 6) (.reg 10)).eval w s4 = some pKept :=
    ev_add (ev_reg (by simp [s4, s3, s2, s1, s0, startState]) hwH0)
      (ev_reg (by simp [s4, hv1]) (by omega)) (by omega)
  let s5 : State := { s4 with regs := Function.update s4.regs 11 pKept }
  have e12 : (Expr.bin .add (.reg 11) (.const 1)).eval w s5 = some kAddr :=
    ev_add (ev_reg (by simp [s5]) (by omega)) (ev_const hw1) (by omega)
  let s6 : State := { s5 with regs := Function.update s5.regs 12 kAddr }
  have e13 : (Expr.bin .add (.reg 12) (.reg 10)).eval w s6 = some dedupH :=
    ev_add (ev_reg (by simp [s6]) (by omega)) (ev_reg (by simp [s6, s5, s4, hv1]) (by omega)) (by omega)
  let s7 : State := { s6 with regs := Function.update s6.regs 13 dedupH }
  have hZ1 : ZeroFrom mem1 dedupH := fun a ha => by
    rw [hout1 a (Or.inr (by omega))]; exact hZ0 a (by omega)
  refine runs_seq_assign_le e11 ?_
  refine runs_seq_assign_le e12 ?_
  refine runs_seq_assign_le e13 ?_
  refine runs_seq_call_le (vs := [h0, xs.length, J.m, kAddr, dedupH]) hfd
    (by simp [evalArgs, Expr.eval, startState, hv1])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨h0, xs.length, J.m, kAddr, dedupH, xs, rfl, rfl, hlist1, hxs_lt_J, hw1, by omega, by omega,
      by omega, hZ1⟩ ?_
  intro v2 mem2 pos2 hpost2
  obtain ⟨hv2, hlist2, hZ2, hlt2, -⟩ := hpost2 h0 xs.length J.m kAddr dedupH xs rfl rfl hlist1
  have hlt2' : ∀ x < kAddr, mem2 x = mem1 x := hlt2
  have hout1' : ∀ x, x < h0 ∨ h0 + xs.length ≤ x → mem1 x = mem x := hout1
  let s8 : State := { mem := mem2, regs := Function.update s7.regs 14 v2, pos := pos2 }
  have hst_a : (Expr.reg 11).eval w s8 = some pKept :=
    ev_reg (by simp [s8, s7, s6, s5]) (by omega)
  have hst_v : (Expr.reg 14).eval w s8 = some kept.length :=
    ev_reg (by simp [s8, hv2, hkept_def]) (by omega)
  let mem2' := Function.update mem2 pKept kept.length
  let s9 : State := { s8 with mem := mem2' }
  have e15 : (Expr.bin .add (.bin .add (.reg 13) (.reg 10)) (.reg 8)).eval w s9 = some pJtilde :=
    ev_add (ev_add (ev_reg (by simp [s9, s8, s7]) (by omega))
      (ev_reg (by simp [s9, s8, s7, s6, s5, s4, hv1]) (by omega)) (by omega))
      (ev_reg (by simp [s9, s8, s7, s6, s5, s4, s3, s2]) (by omega)) (by omega)
  let s10 : State := { s9 with regs := Function.update s9.regs 15 pJtilde }
  have hagr2' : ∀ x < h0, mem2' x = mem x := fun x hx => by
    dsimp only [mem2']
    rw [Function.update_of_ne (by omega), hlt2' x (by omega), hout1' x (Or.inl hx)]
  have hkept2' : ListAt mem2' kAddr kept :=
    ListAt.of_agree hlist2 fun i hi => by
      dsimp only [mem2']; rw [Function.update_of_ne (by omega)]
  have hkeptHdr2' : ListAt mem2' pKept (kept.length :: kept) :=
    listAt_cons_of_head (by dsimp only [mem2']; rw [Function.update_self]) hkept2'
  have hZ2' : ZeroFrom mem2' pJtilde := fun a ha => by
    dsimp only [mem2']; rw [Function.update_of_ne (by omega)]; exact hZ2 a ha
  have hSubPre : SubgraphPre mem2' jAddr kAddr kept.length pJtilde J kept w :=
    ⟨GraphAt.of_agree_below hgJ hJh0 hagr2', hkept2', rfl, hkept_lt, by omega, by omega,
      by omega, hw1⟩
  refine runs_seq_store_le hst_a hst_v ?_
  refine runs_seq_assign_le e15 ?_
  refine runs_seq_call_le (vs := [jAddr, kAddr, kept.length, pJtilde]) hfsub
    (by simp [evalArgs, Expr.eval, startState, hv2, hkept_def])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega)
    ⟨jAddr, kAddr, kept.length, pJtilde, J, kept, rfl, hSubPre⟩ ?_
  intro v3 mem3 pos3 hpost3
  obtain ⟨hGsub, hout3⟩ := hpost3 jAddr kAddr kept.length pJtilde J kept rfl hSubPre
  let s11 : State := { mem := mem3, regs := Function.update s10.regs 16 v3, pos := pos3 }
  have e16 : (Expr.bin .add (.bin .add (.reg 15) (.const 2)) (.bin .add (.reg 14) (.reg 14))).eval w s11 =
      some T := by
    have h15 : (Expr.reg 15).eval w s11 = some pJtilde := ev_reg (by simp [s11, s10]) (by omega)
    have h14 : (Expr.reg 14).eval w s11 = some kept.length :=
      ev_reg (by simp [s11, s10, s9, s8, hv2, hkept_def]) (by omega)
    have ha := ev_add h15 (ev_const (by omega : 2 < 2 ^ w)) (by omega)
    have hb := ev_add h14 h14 (by omega)
    simpa [T, two_mul] using ev_add ha hb (by omega)
  let s12 : State := { s11 with regs := Function.update s11.regs 16 T }
  have hkept3 : ListAt mem3 kAddr kept :=
    ListAt.of_agree hkept2' fun i hi => hout3 _ (Or.inl (by omega))
  have hPosPre : PosTablePre mem3 kAddr kept.length T J.m kept w :=
    ⟨hkept3, rfl, List.nodup_dedup xs, hkept_lt, by omega, by omega, hw1⟩
  refine runs_seq_assign_le e16 ?_
  refine runs_call_le (vs := [kAddr, kept.length, T, J.m]) hfpos
    (by simp [evalArgs, Expr.eval, hv2, hkept_def])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl <;> omega)
    ⟨kAddr, kept.length, T, J.m, kept, rfl, hPosPre⟩ fun v4 mem4 pos4 hpost4 => ?_
  dsimp only [Part1Post]
  obtain ⟨htab, hout4⟩ := hpost4 kAddr kept.length T J.m kept rfl hPosPre
  have hout4' : ∀ x, x < T ∨ T + J.m ≤ x → mem4 x = mem3 x := hout4
  have hout3' : ∀ x, x < pJtilde ∨ pJtilde + 2 + 2 * kept.length ≤ x → mem3 x = mem2' x := hout3
  have hkept_le_xs : kept.length ≤ xs.length := List.Sublist.length_le (List.dedup_sublist xs)
  refine ⟨⟨rfl,
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState],
    by simp, by simp, by simp [L], by simp, by simp, by simp,
    by omega, by omega,
    by change pKept + 1 + kept.length ≤ T + J.m; omega,
    by change pJtilde + (2 + 2 * kept.length) ≤ T + J.m; omega,
    by omega,
    fun x hx => by rw [hout4' x (Or.inl (by omega)), hout3' x (Or.inl (by omega))]; exact hagr2' x hx,
    ListAt.of_agree hkeptHdr2' fun i hi => by
      have hi' : i < kept.length + 1 := by simpa using hi
      rw [hout4' _ (Or.inl (by omega)), hout3' _ (Or.inl (by omega))],
    GraphAt.of_agree_below hGsub
      (by rw [graph_encode_length]; simp only [subgraphOf, Graph.m, List.length_map]
          change pJtilde + (2 + 2 * kept.length) ≤ T; omega)
      (fun x hx => hout4' x (Or.inl hx)),
    htab,
    fun a ha => by rw [hout4' a (Or.inr ha), hout3' a (Or.inr (by omega))]; exact hZ2' a (by omega)⟩, ?_⟩
  simp only [Expr.size, argsSize, flatEdgesContract, dedupListContract, subgraphContract,
    posTableContract, List.getD_cons_succ, List.getD_cons_zero]
  have h1 := Nat.mul_le_mul_left 115 hxs_le
  omega

private def Part2aPost (mem : ℕ → ℕ) (γExp outHdr h0 pKept pJtilde pEmb retHeap : ℕ)
    (J W : Graph) (embWJ embJW : ℕ → Walk) (st : State) : Prop :=
  let kept := (flatEdges embWJ W.m).dedup
  let embJJtilde := compose W (fun eW => (embWJ eW).mapEdges kept.idxOf) embJW
  st.regs 5 = outHdr ∧ st.regs 8 = J.m ∧ st.regs 11 = pKept ∧ st.regs 15 = pJtilde ∧
  st.regs 20 = γExp * (2 * γExp + 3) ∧ st.regs 22 = pEmb ∧
  h0 ≤ pKept ∧ h0 ≤ pJtilde ∧ h0 ≤ pEmb ∧
  pJtilde + (2 + 2 * kept.length) ≤ retHeap ∧
  pKept + 1 + kept.length ≤ retHeap ∧
  pEmb + J.m ≤ retHeap ∧
  retHeap = pEmb + J.m + J.m * (2 + 2 * (γExp * (2 * γExp + 3))) ∧
  retHeap ≤ h0 + sparsifyOutSpace W.m J.m γExp ∧
  (∀ x < h0, st.mem x = mem x) ∧
  ListAt st.mem pKept (kept.length :: kept) ∧
  GraphAt st.mem pJtilde (subgraphOf J kept) ∧
  EmbAt st.mem pEmb J.m embJJtilde ∧
  EmbBounded st.mem pEmb J.m embJJtilde retHeap ∧
  (∀ e < J.m, pEmb ≤ st.mem (pEmb + e)) ∧
  ZeroFrom st.mem retHeap

private lemma sparsifyOut_part2a_runs {w : ℕ} {p : Program} {fmap fcomp : ℕ}
    (hfmap : MeetsContract w p fmap (mapEmbContract w))
    (hfcomp : MeetsContract w p fcomp (composeEmbContract w))
    {mem : ℕ → ℕ} {jAddr bAddr E_WJ E_JW γExp outHdr h0 pKept pJtilde T : ℕ} {ω : ℕ → Bool}
    {J W : Graph} {embWJ embJW : ℕ → Walk} {st₁ : State}
    (hwords : ∀ a ∈ [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0], a < 2 ^ w)
    (hpre : SparsifyOutPre mem jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW w)
    (hp1 : Part1Post mem jAddr bAddr E_WJ E_JW γExp outHdr h0 pKept pJtilde T J W embWJ st₁) :
    ∃ pEmb retHeap o st₂ c₂,
      Runs w p ω (sparsifyOutPart2a fmap fcomp) st₁ o st₂ c₂ ∧
      (o = .normal ∧ Part2aPost mem γExp outHdr h0 pKept pJtilde pEmb retHeap J W embWJ embJW st₂) ∧
      c₂ ≤ W.m * (50 * (2 * γExp + 3) + 200) +
        J.m * (γExp * (120 * (2 * γExp + 3) + 620) + 300) + 180 := by
  obtain ⟨_, hgW, _, hWh0, hEWJ, hBWJ, hEJW, hBJW, hEmbWJ, hEmbJW, hWval, hJn_w, hWn_eq,
    hLenWJ, hLenJW, _, _, hSpw, hw1⟩ := hpre
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r11, r15, r16, h0pK, h0pJt, hpK_E, hpJt_E, hT_le,
    hagr1, hkeptHdr1, hGsub1, htab1, hZ1⟩ := hp1
  set L := 2 * γExp + 3 with hLdef
  set xs := flatEdges embWJ W.m
  set kept := xs.dedup
  set emb' : ℕ → Walk := fun e => if e < W.m then embWJ e else Walk.empty
  obtain ⟨hemb'_eq, _, hemb'_enc⟩ := embWJ_trunc_props hEmbWJ hLenWJ
  have hflat_eq : flatEdges emb' W.m = xs := flatEdges_congr hemb'_eq
  have hsp_exp : sparsifyOutSpace W.m J.m γExp =
      3 + 3 * (W.m * γExp) + 4 * J.m + W.m + W.m * L + L + 2 * (γExp * L) +
        J.m + J.m * (2 + 2 * (γExp * L)) := rfl
  set E_WJtilde := T + J.m with hEWJt_def
  set S := E_WJtilde + W.m + W.m * L with hS_def
  set VB := S + L with hVB_def
  set bufSz := γExp * L with hbuf_def
  set EB := VB + bufSz with hEB_def
  set pEmb := EB + bufSz with hpEmb_def
  set retHeap := pEmb + J.m + J.m * (2 + 2 * bufSz) with hret_def
  have hret_le : retHeap ≤ h0 + sparsifyOutSpace W.m J.m γExp := by omega
  have h0_le_E : h0 ≤ E_WJtilde := by omega
  have hEWJ1 : EmbAt st₁.mem E_WJ W.m emb' := fun e he => by
    simp only [emb', he, ↓reduceIte]; exact (embAt_preserve hEWJ hBWJ hagr1).1 e he
  have hBWJ1 : EmbBounded st₁.mem E_WJ W.m emb' E_WJtilde :=
    ⟨by have := (embAt_preserve hEWJ hBWJ hagr1).2.1; omega,
     fun e he => by
      have := (embAt_preserve hEWJ hBWJ hagr1).2.2 e he
      show st₁.mem (E_WJ + e) + (Walk.encode (emb' e)).length ≤ E_WJtilde
      simp only [emb', he, ↓reduceIte]; omega⟩
  have hMapPre : MapEmbPre st₁.mem E_WJ W.m T E_WJtilde J.m L emb' w :=
    ⟨hEWJ1, hBWJ1, fun e he j hj => (isEmbedding_walk_facts hEmbWJ he).2.2 j (hemb'_eq e he ▸ hj),
      by omega, hemb'_enc, by omega, hw1⟩
  have hwG : γExp < 2 ^ w := hwords γExp (by simp)
  have hwOut : outHdr < 2 ^ w := hwords outHdr (by simp)
  have hwb : bAddr < 2 ^ w := hwords bAddr (by simp)
  have hwEWJ : E_WJ < 2 ^ w := hwords E_WJ (by simp)
  have hwEJW : E_JW < 2 ^ w := hwords E_JW (by simp)
  have e17 : (Expr.bin .add (.reg 16) (.reg 8)).eval w st₁ = some E_WJtilde :=
    ev_add (ev_reg r16 (by omega)) (ev_reg r8 (by omega)) (by omega)
  refine ⟨pEmb, retHeap, ?_⟩
  unfold sparsifyOutPart2a
  refine runs_start_le ?_
  refine runs_seq_assign_le e17 ?_
  refine runs_seq_call_le (vs := [E_WJ, W.m, T, E_WJtilde, J.m, L]) hfmap
    (by simp [evalArgs, Expr.eval, r2, r7, r16, r8, r9])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨E_WJ, W.m, T, E_WJtilde, J.m, L, emb', rfl, hMapPre⟩ ?_
  intro v_m mem2 pos2 hpost2
  obtain ⟨hEmbMap, hBndMap, hout2⟩ := hpost2 E_WJ W.m T E_WJtilde J.m L emb' rfl hMapPre
  have hout2' : ∀ x, x < E_WJtilde ∨ E_WJtilde + W.m + embOffs emb' W.m ≤ x →
      mem2 x = st₁.mem x := hout2
  have hmap_offs : embOffs emb' W.m ≤ W.m * L := embOffs_le hemb'_enc W.m
  let rg1 := Function.update st₁.regs 17 E_WJtilde
  let rg2 := Function.update rg1 18 v_m
  let rg3 := Function.update rg2 18 S
  let rg4 := Function.update rg3 19 VB
  let rg5 := Function.update rg4 20 bufSz
  let rg6 := Function.update rg5 21 EB
  let rg7 := Function.update rg6 22 pEmb
  have e18 : (Expr.bin .add (.bin .add (.reg 17) (.reg 7)) (.bin .mul (.reg 7) (.reg 9))).eval w
      ⟨mem2, rg2, pos2⟩ = some S :=
    ev_add (ev_add (ev_reg (by simp [rg2, rg1]) (by omega)) (ev_reg (by simp [rg2, rg1, r7]) (by omega)) (by omega))
      (ev_mul (ev_reg (by simp [rg2, rg1, r7]) (by omega)) (ev_reg (by simp [rg2, rg1, r9]) (by omega)) (by omega))
      (by omega)
  have e19 : (Expr.bin .add (.reg 18) (.reg 9)).eval w ⟨mem2, rg3, pos2⟩ = some VB :=
    ev_add (ev_reg (by simp [rg3]) (by omega)) (ev_reg (by simp [rg3, rg2, rg1, r9]) (by omega)) (by omega)
  have e20 : (Expr.bin .mul (.reg 4) (.reg 9)).eval w ⟨mem2, rg4, pos2⟩ = some bufSz :=
    ev_mul (ev_reg (by simp [rg4, rg3, rg2, rg1, r4]) hwG) (ev_reg (by simp [rg4, rg3, rg2, rg1, r9]) (by omega))
      (by omega)
  have e21 : (Expr.bin .add (.reg 19) (.reg 20)).eval w ⟨mem2, rg5, pos2⟩ = some EB :=
    ev_add (ev_reg (by simp [rg5, rg4]) (by omega)) (ev_reg (by simp [rg5]) (by omega)) (by omega)
  have e22 : (Expr.bin .add (.reg 21) (.reg 20)).eval w ⟨mem2, rg6, pos2⟩ = some pEmb :=
    ev_add (ev_reg (by simp [rg6]) (by omega)) (ev_reg (by simp [rg6, rg5]) (by omega)) (by omega)
  set embBC := renamedEmb st₁.mem T emb'
  have hBC_eq : ∀ eW < W.m, embBC eW = (embWJ eW).mapEdges kept.idxOf := fun eW heW => by
    have h1 := renamedEmb_eq_idxOf (mem := st₁.mem) (T := T) (emb := emb') (kept := kept) htab1
      (e := eW) (fun j hj => by
        show j ∈ xs.dedup; rw [← hflat_eq]; exact edge_mem_flatEdges_dedup heW hj)
    change renamedEmb st₁.mem T emb' eW = _
    rw [h1]; simp only [emb', heW, ↓reduceIte]
  have hagr2_h0 : ∀ x < h0, mem2 x = mem x := fun x hx =>
    (hout2' x (Or.inl (by omega))).trans (hagr1 x hx)
  have hEJW2 := embAt_preserve hEJW hBJW hagr2_h0
  have hWl : W.encode.length = 2 + 2 * W.m := graph_encode_length W
  have hCompPre : ComposeEmbPre mem2 bAddr E_WJtilde E_JW J.m pEmb S VB EB L γExp W embBC embJW w := by
    refine ⟨GraphAt.of_agree_below hgW hWh0 hagr2_h0, hEmbMap,
      ⟨by have := hBndMap.1; omega, fun e he => by have := hBndMap.2 e he; omega⟩,
      by omega, hEJW2.1,
      ⟨by have := hEJW2.2.1; omega, fun e he => by have := hEJW2.2.2 e he; omega⟩,
      fun e he => (isEmbedding_walk_facts hEmbJW he).1,
      fun e he => (isEmbedding_walk_facts hEmbJW he).2.2,
      fun e he x hx => by
        have hlt := Walk.isWalk_verts_lt hWval (hEmbJW.2 e he) x hx
        omega,
      hLenJW,
      fun j hj => by
        rw [hBC_eq j hj, walk_encode_mapEdges, ← hemb'_eq j hj]
        exact hemb'_enc j,
      fun j hj hne => by
        rw [hBC_eq j hj] at hne ⊢
        exact (isEmbedding_walk_facts hEmbWJ hj).2.1 (by simpa [Walk.mapEdges] using hne),
      by omega, by omega, by omega, by dsimp only [bufSz] at hret_def; omega, hw1⟩
  refine runs_seq_assign_le e18 ?_
  dsimp only
  refine runs_seq_assign_le e19 ?_
  dsimp only
  refine runs_seq_assign_le e20 ?_
  dsimp only
  refine runs_seq_assign_le e21 ?_
  dsimp only
  refine runs_seq_assign_le e22 ?_
  dsimp only
  refine runs_call_le (vs := [bAddr, E_WJtilde, E_JW, J.m, pEmb, S, VB, EB, L, γExp]) hfcomp
    (by simp [evalArgs, Expr.eval, r1, r3, r8, r9, r4])
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    ⟨bAddr, E_WJtilde, E_JW, J.m, pEmb, S, VB, EB, L, γExp, W, embBC, embJW, rfl, hCompPre⟩
    fun v_c mem3 pos3 hpost3 => ?_
  dsimp only [Part2aPost]
  obtain ⟨hEmbC, hBndC, hLoC, hout3⟩ :=
    hpost3 bAddr E_WJtilde E_JW J.m pEmb S VB EB L γExp W embBC embJW rfl hCompPre
  have hout3' : ∀ x, x < S ∨ pEmb + J.m + embOffs (compose W embBC embJW) J.m ≤ x →
      mem3 x = mem2 x := hout3
  have hcomp_offs : embOffs (compose W embBC embJW) J.m ≤ J.m * (2 + 2 * bufSz) :=
    embOffs_compose_le hCompPre.2.2.2.2.2.2.2.2.2.2.1 hLenJW
      (fun e he => (isEmbedding_walk_facts hEmbJW he).2.2) J.m le_rfl
  have hcomp_eq : ∀ e < J.m, compose W embBC embJW e =
      compose W (fun eW => (embWJ eW).mapEdges kept.idxOf) embJW e := fun e he =>
    composeAux_congr W _ _ fun j hj => hBC_eq j ((isEmbedding_walk_facts hEmbJW he).2.2 j hj)
  have hE_le_S : E_WJtilde ≤ S := le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hS_le_pEmb : S ≤ pEmb :=
    le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
  have hpEmb_le_ret : pEmb + J.m ≤ retHeap := Nat.le_add_right _ _
  have hE_le_ret : E_WJtilde ≤ retHeap :=
    le_trans (le_trans hE_le_S hS_le_pEmb) (le_trans (Nat.le_add_right _ _) hpEmb_le_ret)
  have hMapEnd_le_ret : E_WJtilde + W.m + embOffs emb' W.m ≤ retHeap :=
    le_trans (Nat.add_le_add_left hmap_offs _) (le_trans hS_le_pEmb (le_trans (Nat.le_add_right _ _) hpEmb_le_ret))
  have hCompEnd_le_ret : pEmb + J.m + embOffs (compose W embBC embJW) J.m ≤ retHeap :=
    Nat.add_le_add_left hcomp_offs _
  have hpK_E' : pKept + (kept.length + 1) ≤ E_WJtilde := by omega
  refine ⟨⟨rfl, by simp [r5], by simp [r8], by simp [r11], by simp [r15],
    by simp [bufSz, L], by simp, h0pK, h0pJt,
    le_trans (le_trans h0_le_E hE_le_S) hS_le_pEmb, le_trans hpJt_E hE_le_ret,
    le_trans hpK_E hE_le_ret, hpEmb_le_ret, rfl, hret_le,
    fun x hx => by
      have hxE := lt_of_lt_of_le hx h0_le_E
      rw [hout3' x (Or.inl (lt_of_lt_of_le hxE hE_le_S)), hout2' x (Or.inl hxE)]; exact hagr1 x hx,
    ListAt.of_agree hkeptHdr1 fun i hi => by
      have hhiE := lt_of_lt_of_le (Nat.add_lt_add_left (show i < kept.length + 1 by simpa using hi) _) hpK_E'
      rw [hout3' _ (Or.inl (lt_of_lt_of_le hhiE hE_le_S)), hout2' _ (Or.inl hhiE)],
    ListAt.of_agree hGsub1 fun i hi => by
      have hi' : i < 2 + 2 * kept.length := by
        rw [graph_encode_length] at hi; simpa [subgraphOf, Graph.m, kept, xs] using hi
      have hhiE := lt_of_lt_of_le (Nat.add_lt_add_left hi' _) hpJt_E
      rw [hout3' _ (Or.inl (lt_of_lt_of_le hhiE hE_le_S)), hout2' _ (Or.inl hhiE)],
    fun e he => (hcomp_eq e he) ▸ hEmbC e he,
    ⟨hpEmb_le_ret, fun e he => by rw [← hcomp_eq e he]; exact le_trans (hBndC.2 e he) hCompEnd_le_ret⟩,
    hLoC,
    fun a ha => by
      rw [hout3' a (Or.inr (le_trans hCompEnd_le_ret ha)), hout2' a (Or.inr (le_trans hMapEnd_le_ret ha))]
      exact hZ1 a (le_trans hE_le_ret ha)⟩, ?_⟩
  simp only [Expr.size, argsSize, mapEmbContract, composeEmbContract,
    List.getD_cons_succ, List.getD_cons_zero]
  omega

private lemma sparsifyOut_part2b_runs {w : ℕ} {p : Program}
    {mem : ℕ → ℕ} {jAddr bAddr E_WJ E_JW γExp outHdr h0 pKept pJtilde pEmb retHeap : ℕ}
    {ω : ℕ → Bool} {J W : Graph} {embWJ embJW : ℕ → Walk} {st₂ : State}
    (hwords : ∀ a ∈ [jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0], a < 2 ^ w)
    (hpre : SparsifyOutPre mem jAddr bAddr E_WJ E_JW γExp outHdr h0 J W embWJ embJW w)
    (hp2a : Part2aPost mem γExp outHdr h0 pKept pJtilde pEmb retHeap J W embWJ embJW st₂) :
    ∃ o st₃ c₃,
      Runs w p ω sparsifyOutPart2b st₂ o st₃ c₃ ∧
      SparsifyOutPost mem st₃.mem γExp outHdr h0 o.value J W embWJ embJW ∧
      c₃ ≤ 50 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hOuth0, _, hSpw, hw1⟩ := hpre
  obtain ⟨r5, r8, r11, r15, r20, r22, h0pK, h0pJt, h0pE, hpJt_r, hpK_r, hpE_r, hret_eq, hret_le,
    hagr, hkept, hGsub, hEmbC, hBndC, hLoC, hZ⟩ := hp2a
  set bufSz := γExp * (2 * γExp + 3)
  have hret_w : retHeap < 2 ^ w := by omega
  have hbuf_w : 2 + 2 * bufSz < 2 ^ w := by
    have : sparsifyOutSpace W.m J.m γExp =
      3 + 3 * (W.m * γExp) + 4 * J.m + W.m + W.m * (2 * γExp + 3) + (2 * γExp + 3) +
        2 * bufSz + J.m + J.m * (2 + 2 * bufSz) := rfl
    omega
  have hwOut : outHdr < 2 ^ w := hwords outHdr (by simp)
  have e23 : (Expr.bin .add (.bin .add (.reg 22) (.reg 8))
      (.bin .mul (.reg 8) (.bin .add (.const 2) (.bin .add (.reg 20) (.reg 20))))).eval w st₂ =
      some retHeap := by
    have h20 : (Expr.reg 20).eval w st₂ = some bufSz := ev_reg r20 (by omega)
    have h8 : (Expr.reg 8).eval w st₂ = some J.m := ev_reg r8 (by omega)
    have h22 : (Expr.reg 22).eval w st₂ = some pEmb := ev_reg r22 (by omega)
    have h2b : (Expr.bin .add (.const 2) (.bin .add (.reg 20) (.reg 20))).eval w st₂ =
        some (2 + 2 * bufSz) := by
      simpa [two_mul] using ev_add (ev_const (by omega : 2 < 2 ^ w)) (ev_add h20 h20 (by omega)) (by omega)
    simpa [hret_eq] using ev_add (ev_add h22 h8 (by omega)) (ev_mul h8 h2b (by omega)) (by omega)
  let rg9 := Function.update st₂.regs 23 retHeap
  let mA := Function.update st₂.mem outHdr pJtilde
  let mB := Function.update mA (outHdr + 1) pKept
  let mF := Function.update mB (outHdr + 2) pEmb
  have hmF_h0 : ∀ x, h0 ≤ x → mF x = st₂.mem x := fun x hx => by
    dsimp only [mF, mB, mA]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hPostF : SparsifyOutPost mem mF γExp outHdr h0 retHeap J W embWJ embJW := by
    dsimp only [SparsifyOutPost]
    have h0' : mF outHdr = pJtilde := by
      dsimp only [mF, mB, mA]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    have h1' : mF (outHdr + 1) = pKept := by
      dsimp only [mF, mB]; rw [Function.update_of_ne (by omega), Function.update_self]
    have h2' : mF (outHdr + 2) = pEmb := by dsimp only [mF]; rw [Function.update_self]
    rw [h0', h1', h2']
    refine ⟨by omega, by omega, hret_le, fun a ha => by rw [hmF_h0 a (by omega)]; exact hZ a ha,
      h0pJt, h0pK, h0pE,
      by rw [graph_encode_length]; simpa [subgraphOf, Graph.m] using hpJt_r,
      hpK_r, hpE_r, ListAt.of_agree hGsub fun i _ => hmF_h0 _ (by omega),
      ListAt.of_agree hkept fun i _ => hmF_h0 _ (by omega),
      fun e he => by
        have hptr := hLoC e he
        show WalkAt mF (mF (pEmb + e)) _
        rw [hmF_h0 _ (by omega)]
        exact ListAt.of_agree (hEmbC e he) fun i _ => hmF_h0 _ (by omega),
      ⟨hpE_r, fun e he => by rw [hmF_h0 _ (by omega)]; exact hBndC.2 e he⟩,
      fun x hx h0ne h1ne h2ne => by
        dsimp only [mF, mB, mA]
        rw [Function.update_of_ne h2ne, Function.update_of_ne h1ne, Function.update_of_ne h0ne]
        exact hagr x hx⟩
  have hst0_a : (Expr.reg 5).eval w ⟨st₂.mem, rg9, st₂.pos⟩ = some outHdr := ev_reg (by simp [rg9, r5]) hwOut
  have hst0_v : (Expr.reg 15).eval w ⟨st₂.mem, rg9, st₂.pos⟩ = some pJtilde := ev_reg (by simp [rg9, r15]) (by omega)
  have hst1_a : (Expr.bin .add (.reg 5) (.const 1)).eval w ⟨mA, rg9, st₂.pos⟩ = some (outHdr + 1) :=
    ev_add (ev_reg (by simp [rg9, r5]) hwOut) (ev_const hw1) (by omega)
  have hst1_v : (Expr.reg 11).eval w ⟨mA, rg9, st₂.pos⟩ = some pKept := ev_reg (by simp [rg9, r11]) (by omega)
  have hst2_a : (Expr.bin .add (.reg 5) (.const 2)).eval w ⟨mB, rg9, st₂.pos⟩ = some (outHdr + 2) :=
    ev_add (ev_reg (by simp [rg9, r5]) hwOut) (ev_const (by omega : 2 < 2 ^ w)) (by omega)
  have hst2_v : (Expr.reg 22).eval w ⟨mB, rg9, st₂.pos⟩ = some pEmb := ev_reg (by simp [rg9, r22]) (by omega)
  have hret_ev : (Expr.reg 23).eval w ⟨mF, rg9, st₂.pos⟩ = some retHeap := ev_reg (by simp [rg9]) (by omega)
  unfold sparsifyOutPart2b
  refine runs_start_le ?_
  refine runs_seq_assign_le e23 ?_
  refine runs_seq_store_le hst0_a hst0_v ?_
  dsimp only
  refine runs_seq_store_le hst1_a hst1_v ?_
  dsimp only
  refine runs_seq_store_le hst2_a hst2_v ?_
  dsimp only
  refine runs_ret_le hret_ev hPostF ?_
  simp only [Expr.size]; omega

/-- `sparsifyOutBody` meets `sparsifyOutContract w`. -/
theorem sparsifyOut_meetsContract {w : ℕ} {p : Program} {f ff fd fsub fpos fmap fcomp : ℕ}
    (hproc : p.procs[f]? = some (sparsifyOutBody ff fd fsub fpos fmap fcomp))
    (hff : MeetsContract w p ff (flatEdgesContract w))
    (hfd : MeetsContract w p fd (dedupListContract w))
    (hfsub : MeetsContract w p fsub (subgraphContract w))
    (hfpos : MeetsContract w p fpos (posTableContract w))
    (hfmap : MeetsContract w p fmap (mapEmbContract w))
    (hfcomp : MeetsContract w p fcomp (composeEmbContract w)) :
    MeetsContract w p f (sparsifyOutContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨jAddr, bAddr, E_WJ, E_JW, γExp, outHdr, h0, J, W, embWJ, embJW, rfl, hP⟩ := hpre
  obtain ⟨pKept, pJtilde, T, o1, st₁, c₁, hr1, ⟨rfl, hp1⟩, hc1⟩ :=
    sparsifyOut_part1_runs hff hfd hfsub hfpos hwords hP
  obtain ⟨pEmb, retHeap, o2, st₂, c₂, hr2, ⟨rfl, hp2a⟩, hc2⟩ :=
    sparsifyOut_part2a_runs hfmap hfcomp hwords hP hp1
  obtain ⟨o, st₃, c₃, hr3, hp3, hc3⟩ := sparsifyOut_part2b_runs hwords hP hp2a
  have hr23 : Runs w p ω (sparsifyOutPart2a fmap fcomp ;; sparsifyOutPart2b) st₁ o st₃ (c₂ + c₃ + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨st₂, c₂, c₃, hr2, hr3, rfl⟩)
  refine ⟨o, st₃, c₁ + (c₂ + c₃ + 1) + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂ + c₃ + 1, hr1, hr23, rfl⟩), ?_, ?_⟩
  · intro jA' bA' eWJ' eJW' gE' oH' h0' J' W' embWJ' embJW' hargs hP'
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hargs
    have hJeq : J = J' := graphAt_unique hP.1 hP'.1
    have hWeq : W = W' := graphAt_unique hP.2.1 hP'.2.1
    subst hJeq; subst hWeq
    have hWJeq : ∀ e < W.m, embWJ e = embWJ' e := fun e he =>
      walkAt_unique (hP.2.2.2.2.1 e he) (hP'.2.2.2.2.1 e he)
    have hJWeq : ∀ e < J.m, embJW e = embJW' e := fun e he =>
      walkAt_unique (hP.2.2.2.2.2.2.1 e he) (hP'.2.2.2.2.2.2.1 e he)
    have hfl : flatEdges embWJ W.m = flatEdges embWJ' W.m := flatEdges_congr hWJeq
    have hce : ∀ e < J.m,
        compose W (fun eW => (embWJ eW).mapEdges (flatEdges embWJ W.m).dedup.idxOf) embJW e =
        compose W (fun eW => (embWJ' eW).mapEdges (flatEdges embWJ' W.m).dedup.idxOf) embJW' e :=
      fun e he => by
        rw [← hfl]
        simp only [compose, ← hJWeq e he]
        exact composeAux_congr W _ _ fun j hj => by
          rw [hWJeq j ((isEmbedding_walk_facts hP.2.2.2.2.2.2.2.2.2.1 he).2.2 j hj)]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := hp3
    refine ⟨a1, a2, a3, a4, a5, a6, a7, ?_, ?_, a10, ?_, ?_, ?_, ?_, a15⟩
    · simpa [hfl] using a8
    · simpa [hfl] using a9
    · simpa [hfl] using a11
    · simpa [hfl] using a12
    · exact fun e he => (hce e he) ▸ a13 e he
    · exact ⟨a14.1, fun e he => (hce e he) ▸ a14.2 e he⟩
  · have hmW : mem (bAddr + 1) = W.m := by
      simpa [GraphAt, Graph.encode] using hP.2.1 1 (by simp [Graph.encode])
    have hmJ : mem (jAddr + 1) = J.m := by
      simpa [GraphAt, Graph.encode] using hP.1 1 (by simp [Graph.encode])
    simp only [sparsifyOutContract, sparsifyOutCost, List.getD_cons_succ, List.getD_cons_zero,
      hmW, hmJ]
    omega

end MinCostFlow.Spanner
