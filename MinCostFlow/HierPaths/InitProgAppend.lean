module

public import MinCostFlow.HierPaths.InitProgConnChild

/-!
# Appending ordered chunks

A loop appends one chunk at each index. Its invariant is the concatenation of the
chunks already written, and its running time sums the bounds of the individual appends.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The concatenation of the chunks before index `i`. -/
def initAppendPrefix (chunks : ℕ → List ℕ) (i : ℕ) : List ℕ :=
  (List.range i).flatMap chunks

theorem initAppendPrefix_succ (chunks : ℕ → List ℕ) (i : ℕ) :
    initAppendPrefix chunks (i + 1) = initAppendPrefix chunks i ++ chunks i := by
  simp [initAppendPrefix, List.range_succ, List.flatMap_append]

theorem initAppendPrefix_length_mono (chunks : ℕ → List ℕ) {i q : ℕ} (h : i ≤ q) :
    (initAppendPrefix chunks i).length ≤ (initAppendPrefix chunks q).length := by
  induction q, h using Nat.le_induction with
  | base => exact le_rfl
  | succ q h ih =>
    rw [initAppendPrefix_succ, List.length_append]
    exact ih.trans (Nat.le_add_right _ _)

/-- The append loop carries an index-dependent invariant `R`. An append step changes only the
new chunk's cells and returns the new end in register `dstReg`. -/
theorem initAppendIndexedLoop_triple {w : ℕ} {p : Program} {dstReg idxReg : ℕ} {hi : Expr}
    {body : Stmt} (R : ℕ → State → Prop) (chunks : ℕ → List ℕ) (stepCost : ℕ → ℕ)
    (len dst : ℕ) (mem : ℕ → ℕ) (hneq : dstReg ≠ idxReg) (h1 : 1 < 2 ^ w)
    (hlen : len < 2 ^ w)
    (hreg : ∀ s q, R q s → R q { s with regs := Function.update s.regs idxReg q })
    (hhi : ∀ i s, R i s → hi.eval w s = some len)
    (hbody : ∀ i < len, ∀ s, R i s → s.regs idxReg = i →
      s.regs dstReg = dst + (initAppendPrefix chunks i).length →
      (∀ y < dst, s.mem y = mem y) →
      Triple w p (fun t => t = s) body
        (normalPost fun t => R (i + 1) t ∧ t.regs idxReg = i ∧
          t.regs dstReg = dst + (initAppendPrefix chunks (i + 1)).length ∧
          ListAt t.mem (dst + (initAppendPrefix chunks i).length) (chunks i) ∧
          ∀ y, y < dst + (initAppendPrefix chunks i).length ∨
            dst + (initAppendPrefix chunks (i + 1)).length ≤ y → t.mem y = s.mem y)
        (fun _ => stepCost i)) :
    Triple w p (fun s => R 0 s ∧ s.regs dstReg = dst ∧ s.mem = mem)
      (forRange idxReg (.const 0) hi body)
      (normalPost fun t => R len t ∧ t.regs dstReg = dst + (initAppendPrefix chunks len).length ∧
        ListAt t.mem dst (initAppendPrefix chunks len) ∧
        ∀ y, y < dst ∨ dst + (initAppendPrefix chunks len).length ≤ y → t.mem y = mem y)
      (fun _ => rangeCost stepCost 0 len + len * (hi.size + 8) + (hi.size + 6)) := by
  let pref := initAppendPrefix chunks
  let Inv := fun i (s : State) =>
    R i s ∧ s.regs idxReg = i ∧ s.regs dstReg = dst + (pref i).length ∧
    ListAt s.mem dst (pref i) ∧ ∀ y, y < dst ∨ dst + (pref i).length ≤ y → s.mem y = mem y
  have hpref : pref 0 = [] := rfl
  have h := Triple.forRange_le (w := w) (p := p) (r := idxReg) (lo := .const 0) (hi := hi)
    (body := body) (P := fun s => R 0 s ∧ s.regs dstReg = dst ∧ s.mem = mem) (Inv := Inv)
    stepCost 0 len (Nat.zero_le _) h1 (fun _ => hlen)
    (fun s ⟨hr, hd, hm⟩ => by
      refine ⟨Expr.eval_const (Nat.two_pow_pos w), hreg s 0 hr, by simp, ?_, ?_, ?_⟩
      · simp [Function.update_of_ne hneq, hpref, hd]
      · rw [hpref]; intro i hi; simp at hi
      · exact fun _ _ => congrFun hm _)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ s _ _ hI => hhi _ s hI.1)
    (fun i _ hi' => by
      intro s ω ⟨hr, hidx, hptr, hwds, hframe⟩
      obtain ⟨o, t, c, hrun, ht, hcost⟩ :=
        hbody i hi' s hr hidx hptr (fun y hy => hframe y (Or.inl hy)) s ω rfl
      cases o with
      | returned => exact False.elim ht
      | normal =>
        obtain ⟨hR, hix, hp, hchunk, hf⟩ := ht
        refine ⟨.normal, t, c, hrun, ⟨⟨hreg t (i + 1) hR, by simp,
          by simpa [Function.update_of_ne hneq] using hp, ?_, ?_⟩, hix⟩, hcost⟩
        · change ListAt t.mem dst (initAppendPrefix chunks (i + 1))
          rw [initAppendPrefix_succ, listAt_append]
          exact ⟨listAt_congr (fun k hk => (hf _ (Or.inl (by omega))).symm) hwds, hchunk⟩
        · intro y hy
          have hle := initAppendPrefix_length_mono chunks (Nat.le_succ i)
          change y < dst ∨ dst + (initAppendPrefix chunks (i + 1)).length ≤ y at hy
          change (initAppendPrefix chunks i).length ≤ (initAppendPrefix chunks (i + 1)).length at hle
          exact (hf y (by omega)).trans (hframe y (by change y < dst ∨
            dst + (initAppendPrefix chunks i).length ≤ y; omega)))
  refine h.conseq (fun _ hs => hs) ?_ ?_
  · intro o t ht
    cases o with
    | returned => exact False.elim ht
    | normal => exact ⟨ht.1, ht.2.2⟩
  · intro _ _
    simp [Expr.size, Nat.add_comm 1]

/-- The append loop keeps the fixed registers in `R`. An append step changes only the
new chunk's cells and returns the new end in register `dstReg`. -/
theorem initAppendLoop_triple {w : ℕ} {p : Program} {dstReg idxReg : ℕ} {hi : Expr}
    {body : Stmt} (R : State → Prop) (chunks : ℕ → List ℕ) (stepCost : ℕ → ℕ)
    (len dst : ℕ) (mem : ℕ → ℕ) (hneq : dstReg ≠ idxReg) (h1 : 1 < 2 ^ w)
    (hlen : len < 2 ^ w)
    (hreg : ∀ s q, R s → R { s with regs := Function.update s.regs idxReg q })
    (hhi : ∀ s, R s → hi.eval w s = some len)
    (hbody : ∀ i < len, ∀ s, R s → s.regs idxReg = i →
      s.regs dstReg = dst + (initAppendPrefix chunks i).length →
      (∀ y < dst, s.mem y = mem y) →
      Triple w p (fun t => t = s) body
        (normalPost fun t => R t ∧ t.regs idxReg = i ∧
          t.regs dstReg = dst + (initAppendPrefix chunks (i + 1)).length ∧
          ListAt t.mem (dst + (initAppendPrefix chunks i).length) (chunks i) ∧
          ∀ y, y < dst + (initAppendPrefix chunks i).length ∨
            dst + (initAppendPrefix chunks (i + 1)).length ≤ y → t.mem y = s.mem y)
        (fun _ => stepCost i)) :
    Triple w p (fun s => R s ∧ s.regs dstReg = dst ∧ s.mem = mem)
      (forRange idxReg (.const 0) hi body)
      (normalPost fun t => R t ∧ t.regs dstReg = dst + (initAppendPrefix chunks len).length ∧
        ListAt t.mem dst (initAppendPrefix chunks len) ∧
        ∀ y, y < dst ∨ dst + (initAppendPrefix chunks len).length ≤ y → t.mem y = mem y)
      (fun _ => rangeCost stepCost 0 len + len * (hi.size + 8) + (hi.size + 6)) :=
  initAppendIndexedLoop_triple (fun _ => R) chunks stepCost len dst mem hneq h1 hlen
    hreg (fun _ => hhi) hbody

end MinCostFlow.HierPaths

end
