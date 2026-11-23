module

public import MinCostFlow.Spanner.ProgMapList
public import MinCostFlow.Spanner.ProgKeptEdges
public import MinCostFlow.Spanner.Embedding

@[expose] public section

/-!
# Renaming the Edges of an Embedding

The embedding of `W` into `J̃` is the embedding of `W` into `J` with each edge `j` renamed to its
position among the kept edges. This file gives the program that does the renaming for a whole
embedding stored by `EmbAt`. For each walk it writes a pointer, copies the vertex part with
`memCopy`, and renames the edge part with `mapListBody`. The walks are written one after the other
after the new pointer table. The result is `mapEmb_meetsContract`.
-/

namespace MinCostFlow.Spanner

open WordRAM Cited LSF.Program

/-- The total encoded length of the first `k` walks of `emb`. -/
def embOffs (emb : ℕ → Walk) : ℕ → ℕ
  | 0 => 0
  | k + 1 => embOffs emb k + (Walk.encode (emb k)).length

lemma embOffs_le {emb : ℕ → Walk} {L : ℕ} (hL : ∀ e, (Walk.encode (emb e)).length ≤ L) :
    ∀ k, embOffs emb k ≤ k * L
  | 0 => by simp [embOffs]
  | k + 1 => by
    rw [embOffs, Nat.succ_mul]
    have := embOffs_le hL k
    have := hL k
    omega

lemma embOffs_mono (emb : ℕ → Walk) {a b : ℕ} (h : a ≤ b) : embOffs emb a ≤ embOffs emb b := by
  induction b with
  | zero => simp at h; subst h; exact le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · exact (ih (by omega)).trans (by simp [embOffs])
    · rw [show a = b + 1 by omega]

lemma walk_encode_mapEdges (f : ℕ → ℕ) (P : Walk) :
    (Walk.encode (Walk.mapEdges f P)).length = (Walk.encode P).length := by
  simp [walk_encode_length, Walk.mapEdges]

/-- A list stays in place when its cells keep their values. -/
lemma ListAt.of_agree {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l)
    (heq : ∀ i < l.length, mem' (a + i) = mem (a + i)) : ListAt mem' a l :=
  fun i hi => (heq i hi).trans (h i hi)

/-- Procedure body, at `args = [E, m, T, dst, bound, L]`. Here `fc` holds `memCopyStmt` and `fm`
holds `mapListBody`. The last argument is used only by the contract. -/
def mapEmbBody (fc fm : ℕ) : Stmt :=
  .assign 9 (.bin .add (.reg 3) (.reg 1)) ;;
  forRange 5 (.const 0) (.reg 1) (
    .assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
    .assign 7 (.load (.reg 6)) ;;
    .assign 8 (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 7))) ;;
    .store (.bin .add (.reg 3) (.reg 5)) (.reg 9) ;;
    .call 10 fc [.reg 9, .reg 6, .bin .add (.reg 7) (.const 2)] ;;
    .call 10 fm [.bin .add (.bin .add (.reg 6) (.const 2)) (.reg 7), .reg 8, .reg 2,
      .bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7), .reg 4] ;;
    .assign 9 (.bin .add (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7)) (.reg 8))) ;;
  .ret (.const 0)

/-- The walks of `emb` are stored by `EmbAt` at `E`, all below `dst`. Their edges are below
`bound`, the table `[T, T + bound)` is below `dst`, each walk has encoded length at most `L`, and
the output fits in a word. -/
def MapEmbPre (mem : ℕ → ℕ) (E m T dst bound L : ℕ) (emb : ℕ → Walk) (w : ℕ) : Prop :=
  EmbAt mem E m emb ∧ EmbBounded mem E m emb dst ∧ (∀ e < m, ∀ j ∈ (emb e).edges, j < bound) ∧
    T + bound ≤ dst ∧ (∀ e, (Walk.encode (emb e)).length ≤ L) ∧ dst + m + m * L < 2 ^ w ∧
    1 < 2 ^ w

/-- The renamed embedding: each edge `j` becomes the table entry `mem (T + j)`. -/
def renamedEmb (mem : ℕ → ℕ) (T : ℕ) (emb : ℕ → Walk) (e : ℕ) : Walk :=
  Walk.mapEdges (fun j => mem (T + j)) (emb e)

/-- Every edge of the first `k` walks lies in the deduplicated list of their edges. -/
lemma edge_mem_flatEdges_dedup {emb : ℕ → Walk} {k e j : ℕ} (he : e < k)
    (hj : j ∈ (emb e).edges) : j ∈ (flatEdges emb k).dedup := by
  rw [List.mem_dedup]
  unfold flatEdges
  exact List.mem_flatMap.mpr ⟨e, List.mem_range.mpr he, hj⟩

/-- If the table holds the position of each kept edge, and all edges of walk `e` are kept, then
renaming walk `e` through the table renames each edge to its position among the kept edges. -/
lemma renamedEmb_eq_idxOf {mem : ℕ → ℕ} {T : ℕ} {emb : ℕ → Walk} {kept : List ℕ}
    (htab : ∀ j ∈ kept, mem (T + j) = kept.idxOf j) {e : ℕ}
    (hsub : ∀ j ∈ (emb e).edges, j ∈ kept) :
    renamedEmb mem T emb e = (emb e).mapEdges kept.idxOf := by
  simp only [renamedEmb, Walk.mapEdges]
  congr 1
  exact List.map_congr_left fun j hj => htab j (hsub j hj)

/-- Contract of `mapEmbBody`. -/
def mapEmbContract (w : ℕ) : Contract where
  pre args mem := ∃ E m T dst bound L emb, args = [E, m, T, dst, bound, L] ∧
    MapEmbPre mem E m T dst bound L emb w
  post args mem _ mem' := ∀ E m T dst bound L emb, args = [E, m, T, dst, bound, L] →
    MapEmbPre mem E m T dst bound L emb w →
    EmbAt mem' dst m (renamedEmb mem T emb) ∧
      EmbBounded mem' dst m (renamedEmb mem T emb) (dst + m + embOffs emb m) ∧
      ∀ x, x < dst ∨ dst + m + embOffs emb m ≤ x → mem' x = mem x
  cost args _ := args.getD 1 0 * (50 * args.getD 5 0 + 200) + 30

/-- Loop invariant after `k` walks. -/
def MapEmbInv (mem : ℕ → ℕ) (E m T dst bound : ℕ) (emb : ℕ → Walk) (k : ℕ) (st : State) :
    Prop :=
  st.regs 0 = E ∧ st.regs 1 = m ∧ st.regs 2 = T ∧ st.regs 3 = dst ∧ st.regs 4 = bound ∧
    st.regs 5 = k ∧ st.regs 9 = dst + m + embOffs emb k ∧ k ≤ m ∧
    (∀ t < k, st.mem (dst + t) = dst + m + embOffs emb t ∧
      WalkAt st.mem (dst + m + embOffs emb t) (renamedEmb mem T emb t)) ∧
    ∀ x, x < dst ∨ dst + m + embOffs emb k ≤ x → st.mem x = mem x

lemma mapEmb_step {w : ℕ} {p : Program} {fc fm : ℕ}
    (hfc : MeetsContract w p fc (memCopyContract w)) (hfm : MeetsContract w p fm (mapListContract w))
    {mem : ℕ → ℕ} {E m T dst bound L : ℕ} {emb : ℕ → Walk}
    (hpre : MapEmbPre mem E m T dst bound L emb w) (k : ℕ) (hk : k < m) :
    Triple w p (MapEmbInv mem E m T dst bound emb k)
      (.assign 6 (.load (.bin .add (.reg 0) (.reg 5))) ;;
        .assign 7 (.load (.reg 6)) ;;
        .assign 8 (.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 7))) ;;
        .store (.bin .add (.reg 3) (.reg 5)) (.reg 9) ;;
        .call 10 fc [.reg 9, .reg 6, .bin .add (.reg 7) (.const 2)] ;;
        .call 10 fm [.bin .add (.bin .add (.reg 6) (.const 2)) (.reg 7), .reg 8, .reg 2,
          .bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7), .reg 4] ;;
        .assign 9 (.bin .add (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7)) (.reg 8)))
      (normalPost fun st₁ =>
        MapEmbInv mem E m T dst bound emb (k + 1)
          { st₁ with regs := Function.update st₁.regs 5 (k + 1) } ∧ st₁.regs 5 = k)
      (fun _ => 50 * L + 180) := by
  obtain ⟨hEmb, hBnd, hEdg, hTd, hL, hdw, hw1⟩ := hpre
  intro st ω hI
  obtain ⟨r0, r1, r2, r3, r4, r5, r9, hkm, hdone, hout⟩ := hI
  have hoffs := embOffs_le hL k
  have hkL : k * L + L ≤ m * L := by
    have := Nat.mul_le_mul_right L (show k + 1 ≤ m by omega); rw [Nat.succ_mul] at this; exact this
  set cur := dst + m + embOffs emb k with hcur
  have hEk : E + k < dst := by have := hBnd.1; omega
  set P := mem (E + k) with hP
  obtain ⟨hnv, hverts, hne, hedges⟩ := walkAt_iff.mp (hEmb k hk)
  have hPb := hBnd.2 k hk
  have hLk := hL k
  rw [walk_encode_length] at hPb hLk
  set nv := (emb k).verts.length with hnvdef
  set ne := (emb k).edges.length with hnedef
  have hst : ∀ x, x < dst → st.mem x = mem x := fun x hx => hout x (Or.inl hx)
  have hwd : dst < 2 ^ w := by omega
  have hcw : cur + 2 + nv + ne < 2 ^ w := by omega
  -- Loading the pointer and the two counts of walk `k`.
  have e6 : (Expr.load (.bin .add (.reg 0) (.reg 5))).eval w st = some P :=
    ev_load (ev_add (ev_reg r0 (by omega)) (ev_reg r5 (by omega)) (by omega)) (hst _ hEk)
      (by omega)
  let s1 : State := { st with regs := Function.update st.regs 6 P }
  have e7 : (Expr.load (.reg 6)).eval w s1 = some nv :=
    ev_load (ev_reg (v := P) (by simp [s1]) (by omega))
      (by simp only [s1]; rw [hst P (by omega)]; exact hnv) (by omega)
  let s2 : State := { s1 with regs := Function.update s1.regs 7 nv }
  have e8 : (Expr.load (.bin .add (.bin .add (.reg 6) (.const 1)) (.reg 7))).eval w s2 =
      some ne :=
    ev_load (ev_add (ev_add (ev_reg (v := P) (by simp [s2, s1]) (by omega)) (ev_const hw1)
      (by omega)) (ev_reg (v := nv) (by simp [s2]) (by omega)) (by omega))
      (by simp only [s2, s1]; rw [hst (P + 1 + nv) (by omega)]; exact hne) (by omega)
  let s3 : State := { s2 with regs := Function.update s2.regs 8 ne }
  have esa : (Expr.bin .add (.reg 3) (.reg 5)).eval w s3 = some (dst + k) :=
    ev_add (ev_reg (v := dst) (by simp [s3, s2, s1, r3]) hwd)
      (ev_reg (v := k) (by simp [s3, s2, s1, r5]) (by omega)) (by omega)
  have esv : (Expr.reg 9).eval w s3 = some cur :=
    ev_reg (v := cur) (by simp [s3, s2, s1, r9]) (by omega)
  let s4 : State := { s3 with mem := Function.update s3.mem (dst + k) cur }
  have hs4 : ∀ x, x ≠ dst + k → s4.mem x = st.mem x := fun x hx => by
    simp only [s4, s3, s2, s1]; rw [Function.update_of_ne hx]
  have hargs1 : evalArgs w s4 [.reg 9, .reg 6, .bin .add (.reg 7) (.const 2)] =
      some [cur, P, nv + 2] := by
    have a1 : (Expr.reg 9).eval w s4 = some cur :=
      ev_reg (v := cur) (by simp [s4, s3, s2, s1, r9]) (by omega)
    have a2 : (Expr.reg 6).eval w s4 = some P :=
      ev_reg (v := P) (by simp [s4, s3, s2, s1]) (by omega)
    have a3 : (Expr.bin .add (.reg 7) (.const 2)).eval w s4 = some (nv + 2) :=
      ev_add (ev_reg (v := nv) (by simp [s4, s3, s2]) (by omega)) (ev_const (c := 2) (by omega))
        (by omega)
    simp [evalArgs, a1, a2, a3]
  refine runs_start_le ?_
  refine runs_seq_assign_le e6 ?_
  refine runs_seq_assign_le e7 ?_
  refine runs_seq_assign_le e8 ?_
  refine runs_seq_store_le esa esv ?_
  refine runs_seq_call_le hfc hargs1 ?_ ⟨cur, P, nv + 2, rfl, by omega, by omega,
    Or.inr (by omega)⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨d', s', l', hargs', -, hcopy0, hother0⟩ := hpost₁
  simp only [List.cons.injEq, and_true] at hargs'
  obtain ⟨hd', hs', hl'⟩ := hargs'
  subst hd' hs' hl'
  have hcopy : ∀ i < nv + 2, mem₁ (cur + i) = s4.mem (P + i) := hcopy0
  have hother₁ : ∀ x, x < cur ∨ cur + (nv + 2) ≤ x → mem₁ x = s4.mem x := hother0
  -- Below `dst` the memory after the copy is the starting memory.
  have hlow₁ : ∀ x, x < dst → mem₁ x = mem x := fun x hx => by
    rw [hother₁ x (Or.inl (by omega)), hs4 x (by omega), hst x hx]
  let s5 : State := { mem := mem₁, regs := Function.update s4.regs 10 v₁, pos := pos₁ }
  have hargs2 : evalArgs w s5 [.bin .add (.bin .add (.reg 6) (.const 2)) (.reg 7), .reg 8, .reg 2,
      .bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7), .reg 4] =
      some [P + 2 + nv, ne, T, cur + 2 + nv, bound] := by
    have a1 : (Expr.bin .add (.bin .add (.reg 6) (.const 2)) (.reg 7)).eval w s5 =
        some (P + 2 + nv) :=
      ev_add (ev_add (ev_reg (v := P) (by simp [s5, s4, s3, s2, s1]) (by omega))
        (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := nv) (by simp [s5, s4, s3, s2]) (by omega)) (by omega)
    have a2 : (Expr.reg 8).eval w s5 = some ne :=
      ev_reg (v := ne) (by simp [s5, s4, s3]) (by omega)
    have a3 : (Expr.reg 2).eval w s5 = some T :=
      ev_reg (v := T) (by simp [s5, s4, s3, s2, s1, r2]) (by omega)
    have a4 : (Expr.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7)).eval w s5 =
        some (cur + 2 + nv) :=
      ev_add (ev_add (ev_reg (v := cur) (by simp [s5, s4, s3, s2, s1, r9]) (by omega))
        (ev_const (c := 2) (by omega)) (by omega))
        (ev_reg (v := nv) (by simp [s5, s4, s3, s2]) (by omega)) (by omega)
    have a5 : (Expr.reg 4).eval w s5 = some bound :=
      ev_reg (v := bound) (by simp [s5, s4, s3, s2, s1, r4]) (by omega)
    simp [evalArgs, a1, a2, a3, a4, a5]
  have hpre2 : MapListPre mem₁ (P + 2 + nv) ne T (cur + 2 + nv) bound (emb k).edges w :=
    ⟨ListAt.of_agree hedges fun i hi => hlow₁ _ (by omega), rfl,
      fun j hj => hEdg k hk j hj, by omega, by omega, by omega, hw1⟩
  refine runs_seq_call_le hfm hargs2 ?_ ⟨_, _, _, _, _, _, rfl, hpre2⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨hmap0, hother0₂⟩ := hpost₂ _ _ _ _ _ _ rfl hpre2
  have hmap : ListAt mem₂ (cur + 2 + nv) ((emb k).edges.map fun x => mem₁ (T + x)) := hmap0
  have hother₂ : ∀ x, x < cur + 2 + nv ∨ cur + 2 + nv + ne ≤ x → mem₂ x = mem₁ x := hother0₂
  have e9 : (Expr.bin .add (.bin .add (.bin .add (.reg 9) (.const 2)) (.reg 7)) (.reg 8)).eval w
      { mem := mem₂, regs := Function.update s5.regs 10 v₂, pos := pos₂ } =
      some (cur + 2 + nv + ne) :=
    ev_add (ev_add (ev_add (ev_reg (v := cur) (by simp [s5, s4, s3, s2, s1, r9]) (by omega))
      (ev_const (c := 2) (by omega)) (by omega))
      (ev_reg (v := nv) (by simp [s5, s4, s3, s2]) (by omega)) (by omega))
      (ev_reg (v := ne) (by simp [s5, s4, s3]) (by omega)) (by omega)
  -- How the final memory looks.
  have hfin_low : ∀ x, x < cur → x ≠ dst + k → mem₂ x = st.mem x := fun x hx hne' => by
    rw [hother₂ x (Or.inl (by omega)), hother₁ x (Or.inl (by omega)), hs4 x hne']
  have hfin_copy : ∀ i < nv + 2, mem₂ (cur + i) = mem (P + i) := fun i hi => by
    rw [hother₂ _ (Or.inl (by omega)), hcopy i hi, hs4 _ (by omega), hst _ (by omega)]
  have hoffs_succ : embOffs emb (k + 1) = embOffs emb k + (2 + nv + ne) := by
    rw [embOffs, walk_encode_length]
  refine runs_assign_le e9 ⟨⟨?_, ?_, ?_, ?_, ?_, by simp, ?_, by omega, ?_, ?_⟩,
    by simp [s5, s4, s3, s2, s1, r5]⟩ ?_
  · simp [s5, s4, s3, s2, s1, r0]
  · simp [s5, s4, s3, s2, s1, r1]
  · simp [s5, s4, s3, s2, s1, r2]
  · simp [s5, s4, s3, s2, s1, r3]
  · simp [s5, s4, s3, s2, s1, r4]
  · simp only [Function.update_self, Function.update_of_ne (show (9 : ℕ) ≠ 5 by omega)]
    rw [hoffs_succ]; omega
  · intro t ht
    dsimp only
    rcases Nat.lt_or_ge t k with htk | htk
    · -- An earlier walk: its cells and its pointer keep their values.
      obtain ⟨hptr, hwalk⟩ := hdone t htk
      have hmono := embOffs_mono emb (show t + 1 ≤ k by omega)
      have hlen : (Walk.encode (renamedEmb mem T emb t)).length = (Walk.encode (emb t)).length :=
        walk_encode_mapEdges _ _
      rw [embOffs] at hmono
      refine ⟨?_, ListAt.of_agree hwalk fun i hi => ?_⟩
      · rw [hfin_low _ (by omega) (by omega)]; exact hptr
      · rw [hfin_low _ (by omega) (by omega)]
    · -- The new walk `k`.
      have htk' : t = k := by omega
      rw [htk']
      refine ⟨?_, ?_⟩
      · rw [hother₂ _ (Or.inl (by omega)), hother₁ _ (Or.inl (by omega))]
        show Function.update st.mem (dst + k) cur (dst + k) = cur
        rw [Function.update_self]
      · rw [walkAt_iff]
        simp only [renamedEmb, Walk.mapEdges, List.length_map]
        refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
        · rw [← hcur, show cur = cur + 0 by rfl, hfin_copy 0 (by omega)]; exact hnv
        · rw [← hcur, Nat.add_assoc, hfin_copy (1 + i) (by omega), ← Nat.add_assoc]
          exact hverts i hi
        · rw [← hcur, Nat.add_assoc, hfin_copy (1 + nv) (by omega), ← Nat.add_assoc]
          exact hne
        · rw [← hcur]
          have hmapeq : (emb k).edges.map (fun x => mem₁ (T + x)) =
              (emb k).edges.map (fun j => mem (T + j)) :=
            List.map_congr_left fun x hx => hlow₁ _ (by have := hEdg k hk x hx; omega)
          rw [← hmapeq]; exact hmap
  · intro x hx
    dsimp only
    rw [hoffs_succ] at hx
    rw [hother₂ x (by omega), hother₁ x (by omega), hs4 x (by omega)]
    exact hout x (by omega)
  · simp only [Expr.size, argsSize, memCopyContract, mapListContract, List.getD_cons_succ,
      List.getD_cons_zero]
    omega

lemma embOffs_congr {e₁ e₂ : ℕ → Walk} :
    ∀ {k : ℕ}, (∀ j < k, e₁ j = e₂ j) → embOffs e₁ k = embOffs e₂ k
  | 0, _ => rfl
  | k + 1, h => by
    rw [embOffs, embOffs, embOffs_congr (fun j hj => h j (by omega)), h k (by omega)]

/-- `mapEmbBody fc fm` at `f` meets `mapEmbContract`, given that `fc` holds `memCopyStmt` and
`fm` holds `mapListBody`. The cost is `m (50 L + 200) + 30`. -/
theorem mapEmb_meetsContract {w : ℕ} {p : Program} {f fc fm : ℕ}
    (hproc : p.procs[f]? = some (mapEmbBody fc fm))
    (hfc : MeetsContract w p fc (memCopyContract w))
    (hfm : MeetsContract w p fm (mapListContract w)) :
    MeetsContract w p f (mapEmbContract w) := by
  refine meetsContract_of_runs hproc fun args mem pos ω hwords hpre => ?_
  obtain ⟨E, m, T, dst, bound, L, emb, rfl, hP⟩ := hpre
  have hP' := hP
  obtain ⟨hEmb, hBnd, hEdg, hTd, hL, hdw, hw1⟩ := hP'
  have hmw : m < 2 ^ w := hwords m (by simp)
  have hloop := Triple.forRange_const (p := p) (w := w) (r := 5) (lo := .const 0) (hi := .reg 1)
    (P := fun st => st.regs 0 = E ∧ st.regs 1 = m ∧ st.regs 2 = T ∧ st.regs 3 = dst ∧
      st.regs 4 = bound ∧ st.regs 9 = dst + m ∧ st.mem = mem)
    (Inv := MapEmbInv mem E m T dst bound emb) (50 * L + 180) 0 m (Nat.zero_le _) hw1
    (fun _ => hmw)
    (fun st ⟨q0, q1, q2, q3, q4, q9, hm⟩ => ⟨ev_const (by omega),
      ⟨by simp [q0], by simp [q1], by simp [q2], by simp [q3], by simp [q4], by simp,
        by simp [q9, embOffs], Nat.zero_le _, fun t ht => absurd ht (Nat.not_lt_zero _),
        fun x _ => by simp [hm]⟩⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ _ _ _ h => ev_reg h.2.1 hmw)
    (fun k _ hk => mapEmb_step hfc hfm hP k hk)
  have e9 : (Expr.bin .add (.reg 3) (.reg 1)).eval w
      (startState [E, m, T, dst, bound, L] mem pos) = some (dst + m) :=
    ev_add (ev_reg (v := dst) (by simp [startState]) (by omega))
      (ev_reg (v := m) (by simp [startState]) hmw) (by omega)
  refine runs_start_le ?_
  refine runs_seq_assign_le e9 ?_
  refine runs_seq_triple_le hloop ⟨by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp, rfl⟩ ?_
  intro st₁ hI
  obtain ⟨-, -, -, -, -, -, -, -, hdone, hout⟩ := hI
  refine runs_ret_le (v := 0) (ev_const (by omega))
    (fun E' m' T' d' b' L' emb' h1 h2 => ?_) ?_
  · simp only [List.cons.injEq, and_true] at h1
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
    have hEq : ∀ j < m, emb j = emb' j := fun j hj => walkAt_unique (hEmb j hj) (h2.1 j hj)
    have hR : ∀ j < m, renamedEmb mem T emb' j = renamedEmb mem T emb j := fun j hj => by
      simp only [renamedEmb, hEq j hj]
    rw [← embOffs_congr hEq]
    refine ⟨fun j hj => ?_, ⟨by omega, fun j hj => ?_⟩, hout⟩
    · rw [hR j hj, (hdone j hj).1]; exact (hdone j hj).2
    · rw [hR j hj, (hdone j hj).1, renamedEmb, walk_encode_mapEdges]
      have hmono := embOffs_mono emb (show j + 1 ≤ m by omega)
      rw [embOffs] at hmono
      omega
  · simp only [Expr.size, mapEmbContract, List.getD_cons_succ, List.getD_cons_zero,
      Nat.sub_zero]
    nlinarith [Nat.mul_le_mul_left m (show 50 * L + 180 + 1 + 8 ≤ 50 * L + 200 by omega)]

end MinCostFlow.Spanner
