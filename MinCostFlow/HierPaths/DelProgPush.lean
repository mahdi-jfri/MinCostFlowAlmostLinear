module

public import MinCostFlow.HierPaths.DelProgIneligBit

/-!
# Appending to the connector work list

A connector whose old bit was clear is appended to scratch space. The append preserves the
block and every scratch cell except the newly written slot.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Append the connector in register `31`, with base and length in `33` and `34`. -/
def delConnPush : Stmt :=
  .seq (.store (.bin .add (.reg 33) (.reg 34)) (.reg 31))
    (.assign 34 (.bin .add (.reg 34) (.const 1)))

/-- Append one connector and advance the work-list length in constant time. -/
theorem delConnPush_triple {w : ℕ} {p : Program} {b base c : ℕ} {block L : List ℕ}
    {R mem0 : ℕ → ℕ} (hbase : R 33 = base) (hcount : R 34 = L.length)
    (hc : R 31 = c) (hdisj : b + block.length ≤ base) (hw : base + L.length + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b block ∧ ListAt s.mem base L ∧ s.mem = mem0)
      delConnPush
      (normalPost fun s => s.regs = Function.update R 34 (L.length + 1) ∧
        ListAt s.mem b block ∧ ListAt s.mem base (L ++ [c]) ∧
        s.mem = Function.update mem0 (base + L.length) c)
      (fun _ => 12) := by
  let M := fun mem => ListAt mem b block ∧ ListAt mem base (L ++ [c]) ∧
    mem = Function.update mem0 (base + L.length) c
  have hstore : Triple w p
      (fun s => s.regs = R ∧ ListAt s.mem b block ∧ ListAt s.mem base L ∧ s.mem = mem0)
      (.store (.bin .add (.reg 33) (.reg 34)) (.reg 31))
      (normalPost fun s => s.regs = R ∧ M s.mem)
      (fun _ => (Expr.bin .add (.reg 33) (.reg 34)).size + (Expr.reg 31).size + 1) := by
    refine Triple.store (addr := fun _ => base + L.length) (val := fun _ => c)
      (fun s hs => Expr.eval_add (Expr.eval_reg_of_eq (by rw [hs.1, hbase]))
        (Expr.eval_reg_of_eq (by rw [hs.1, hcount])) (by omega))
      (fun s hs => Expr.eval_reg_of_eq (by rw [hs.1, hc])) (fun s hs => ?_)
    obtain ⟨hr, hblk, hL, hmem⟩ := hs
    refine ⟨hr, ?_, listAt_append_one hL c, by rw [hmem]⟩
    refine listAt_congr (fun k hk => ?_) hblk
    exact (Function.update_of_ne (by omega) _ _).symm
  unfold delConnPush
  refine (Triple.seq_normal_const hstore (triple_assign_exact (M := M) ?_)).mono_cost ?_
  · intro s hs _
    exact Expr.eval_add (Expr.eval_reg_of_eq (by rw [hs, hcount]))
      (Expr.eval_const (by omega)) (by omega)
  · intro s hs
    decide

theorem delConnPush_noRand : delConnPush.NoRand := by
  simp [delConnPush, Stmt.NoRand]

/-- Mark a connector and append it to the work list only on the first visit. -/
def delConnVisit : Stmt :=
  .seq delIneligBit (.cond (.reg 32) .nop delConnPush)

theorem delConnVisit_noRand : delConnVisit.NoRand := by
  simp [delConnVisit, Stmt.NoRand, delIneligBit_noRand, delConnPush_noRand]

/-- After one visit, the mark and work list agree, and other memory is preserved. -/
theorem delConnVisit_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base c : ℕ} {L : List ℕ} {R mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hcR : R 31 = c) (hbase : R 33 = base) (hcount : R 34 = L.length)
    (hc : c < x.H.A.C.numConn) (hdisj : b + x.encode.length ≤ base)
    (hw : base + L.length + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ListAt s.mem base L ∧ s.mem = mem0)
      delConnVisit (normalPost fun s =>
        let out := L ++ delCollect x.ms.st.inelig [c]
        s.regs = Function.update (Function.update R 32 (if c ∈ x.ms.st.inelig then 1 else 0))
          34 out.length ∧ ListAt s.mem b (x.markInelig c).encode ∧ ListAt s.mem base out ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → (i < base + L.length ∨ base + out.length ≤ i) →
          s.mem i = mem0 i)
      (fun _ => 65) := by
  let old := if c ∈ x.ms.st.inelig then 1 else 0
  let R' := Function.update R 32 old
  let out := L ++ delCollect x.ms.st.inelig [c]
  let P := fun s : State => s.regs = R' ∧ ListAt s.mem b (x.markInelig c).encode ∧
    ListAt s.mem base L ∧
      ∀ i, (i < b ∨ b + x.encode.length ≤ i) → s.mem i = mem0 i
  let Q := fun s : State => s.regs = Function.update R' 34 out.length ∧
    ListAt s.mem b (x.markInelig c).encode ∧ ListAt s.mem base out ∧
    ∀ i, (i < b ∨ b + x.encode.length ≤ i) → (i < base + L.length ∨ base + out.length ≤ i) →
      s.mem i = mem0 i
  have hb : b + x.encode.length < 2 ^ w := by omega
  have hpre : Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
      ListAt s.mem base L ∧ s.mem = mem0) delIneligBit (normalPost P) (fun _ => 45) := by
    intro s ω hs
    obtain ⟨o, s', k, hrun, h, hk⟩ :=
      delIneligBit_triple (w := w) (p := p) (mem0 := mem0) x hR0 hcR hc hb s ω ⟨hs.1, hs.2.1, hs.2.2.2⟩
    cases o <;> try contradiction
    obtain ⟨hr, hblock, hframe⟩ := h
    refine ⟨_, s', k, hrun, ?_, hk⟩
    refine ⟨hr, hblock, listAt_congr (fun k hk => ?_) hs.2.2.1, hframe⟩
    exact (congrFun hs.2.2.2 _).trans (hframe _ (Or.inr (by omega))).symm
  have hr32 : ∀ s, P s → s.regs 32 = old := fun s hs => by simp [hs.1, R']
  have hpost : Triple w p P (.cond (.reg 32) .nop delConnPush) (normalPost Q)
      (fun _ => 15) := by
    refine (Triple.cond (val := fun s => s.regs 32) (fun _ _ => Expr.eval_reg_of_eq rfl)
      (T_t := fun _ => 1) (T_f := fun _ => 12) (Triple.nop ?_) ?_).mono_cost ?_
    · intro s ⟨hs, hn⟩
      have hm : c ∈ x.ms.st.inelig := by
        by_contra h; exact hn (by simp [hr32 s hs, old, h])
      have ho : out = L := by simp [out, delCollect, hm]
      obtain ⟨hr, hblock, hL, hf⟩ := hs
      refine ⟨?_, hblock, ho ▸ hL, fun i h _ => hf i h⟩
      rw [hr, ho]
      exact (Function.update_eq_self_iff.mpr (by simpa [R'] using hcount.symm)).symm
    · intro s ω ⟨hs, hz⟩
      have hm : c ∉ x.ms.st.inelig := by
        intro h; simp [hr32 s hs, old, h] at hz
      have ho : out = L ++ [c] := by simp [out, delCollect, hm]
      have hd : b + (x.markInelig c).encode.length ≤ base :=
        (congrArg (b + ·) (x.length_encode_markInelig c)).le.trans hdisj
      have H := delConnPush_triple (w := w) (p := p) (b := b) (R := R') (mem0 := s.mem)
        (base := base) (c := c) (L := L) (block := (x.markInelig c).encode) (by simpa [R'] using hbase)
        (by simpa [R'] using hcount) (by simpa [R'] using hcR)
        hd hw
      obtain ⟨o, s', k, hrun, h, hk⟩ := H s ω ⟨hs.1, hs.2.1, hs.2.2.1, rfl⟩
      cases o <;> try contradiction
      refine ⟨_, s', k, hrun, ?_, hk⟩
      obtain ⟨hr, hb', hL, hmem⟩ := h
      refine ⟨by simpa [ho] using hr, hb', ho ▸ hL, fun i hi hwi => ?_⟩
      have hne : i ≠ base + L.length := by rw [ho, List.length_append] at hwi; simp at hwi; omega
      rw [hmem, Function.update_of_ne hne]
      exact hs.2.2.2 i hi
    · intro s hs
      split <;> decide
  exact (Triple.seq_normal_const hpre hpost).mono_cost fun _ _ => by decide

/-- Visit the connector at the current incident-list word in register `35`. -/
def delConnAt : Stmt :=
  .seq (.assign 31 (readSec numSec 0 7 (.reg 35))) delConnVisit

theorem delConnAt_noRand : delConnAt.NoRand := by
  simp [delConnAt, Stmt.NoRand, delConnVisit_noRand]

/-- Reading one incident-list word and visiting it preserves the other list entries. -/
theorem delConnAt_triple {w : ℕ} {p : Program} (x : HierConcrete)
    {b base c k : ℕ} {L : List ℕ} {R mem0 : ℕ → ℕ}
    (hR0 : R 0 = b) (hkR : R 35 = k) (hbase : R 33 = base) (hcount : R 34 = L.length)
    (hk : k < (x.sections.getD 7 []).length) (hword : (x.sections.getD 7 [])[k] = c)
    (hc : c < x.H.A.C.numConn) (hdisj : b + x.encode.length ≤ base)
    (hw : base + L.length + 1 < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ ListAt s.mem b x.encode ∧
        ListAt s.mem base L ∧ s.mem = mem0)
      delConnAt (normalPost fun s =>
        let out := L ++ delCollect x.ms.st.inelig [c]
        s.regs = Function.update (Function.update (Function.update R 31 c) 32
          (if c ∈ x.ms.st.inelig then 1 else 0)) 34 out.length ∧
        ListAt s.mem b (x.markInelig c).encode ∧ ListAt s.mem base out ∧
        ∀ i, (i < b ∨ b + x.encode.length ≤ i) → (i < base + L.length ∨ base + out.length ≤ i) →
          s.mem i = mem0 i)
      (fun _ => 90) := by
  have hb : b + x.encode.length < 2 ^ w := by omega
  let M := fun mem => ListAt mem b x.encode ∧ ListAt mem base L ∧ mem = mem0
  have hread : Triple w p (fun s => s.regs = R ∧ M s.mem)
      (.assign 31 (readSec numSec 0 7 (.reg 35)))
      (normalPost fun s => s.regs = Function.update R 31 c ∧ M s.mem)
      (fun _ => (readSec numSec 0 7 (.reg 35)).size + 1) := by
    refine triple_assign_exact fun s hr hm => ?_
    have H := eval_readSec (w := w)
      (show ListAt s.mem b (layoutList x.sections) from hm.1)
      hb (by rw [hr, hR0]) (i := 7) (by rw [x.length_sections']; norm_num)
      (Expr.eval_reg_of_eq (v := k) (by rw [hr, hkR])) hk
    rwa [x.length_sections', hword] at H
  unfold delConnAt
  refine (Triple.seq_normal_const hread
    (delConnVisit_triple (p := p) (mem0 := mem0) x (by simpa using hR0) (by simp)
      (by simpa using hbase) (by simpa using hcount) hc hdisj hw)).mono_cost ?_
  intro s hs
  decide

end MinCostFlow.HierPaths

end
