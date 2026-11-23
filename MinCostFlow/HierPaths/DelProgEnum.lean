module

public import MinCostFlow.HierPaths.DelProgCounter

/-!
# Enumerating a full group in the `Delete` program

When the own count of a group `X` reaches its size, `levelStep` enumerates its members
(`enumerate`, `HierPaths/LossCounters.lean`): it marks them globally lost and outputs those not
marked before. The members are the terminals `X · sz, …, X · sz + sz - 1`, with `sz` the group size.

`enumStmt` does this with the group in register `14` and its size in register `15`, as `ctrStmt`
leaves them. For each member `v` it reads the lost bit of `v` (section 14). If the bit is clear,
it sets it and appends `v` to a work list in memory: the work list starts at the address in
register `22` and holds as many words as register `23` says. `enum_triple` gives the result: the
block of the concrete state with the members added to the lost set, the work list extended by the
members that were not lost, and every other cell unchanged.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

/-- The concrete state with the lost set replaced by `G`. -/
def HierConcrete.withGlob (x : HierConcrete) (G : Finset ℕ) : HierConcrete :=
  x.withSt { x.ms.st with loss := { x.ms.st.loss with glob := G } }

/-- Appending a word to a list in memory. -/
theorem listAt_append_one {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l) (v : ℕ) :
    ListAt (Function.update mem (a + l.length) v) a (l ++ [v]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  by_cases hil : i < l.length
  · rw [Function.update_of_ne (by omega), List.getElem_append_left hil]; exact h i hil
  · have : i = l.length := by omega
    subst this
    simp

/-- The body: test the lost bit of the member in register `20`; if clear, set it and append the
member to the work list. -/
def enumBody : Stmt :=
  .seq (.assign 24 (readSec numSec 0 14 (.reg 20)))
    (.cond (.reg 24) .nop
      (.seq (.store (secAddr numSec 0 14 (.reg 20)) (.const 1))
        (.seq (.store (.bin .add (.reg 22) (.reg 23)) (.reg 20))
          (.assign 23 (.bin .add (.reg 23) (.const 1))))))

/-- Enumerate the members of the group in register `14`, of size in register `15`. -/
def enumStmt : Stmt :=
  .seq (.assign 21 (.bin .add (.bin .mul (.reg 14) (.reg 15)) (.reg 15)))
    (forRange 20 (.bin .mul (.reg 14) (.reg 15)) (.reg 21) enumBody)

theorem enumStmt_noRand : enumStmt.NoRand := by
  simp [enumStmt, enumBody, forRange, forUp, Stmt.NoRand]

theorem length_layoutList_set (bs : List (List ℕ)) {i : ℕ} {l : List ℕ}
    (hl : l.length = (bs.getD i []).length) :
    (layoutList (bs.set i l)).length = (layoutList bs).length := by
  have key : ∀ (cs : List (List ℕ)), (layoutList cs).length =
      cs.length + 1 + ((List.range cs.length).map fun j => (cs.getD j []).length).sum := by
    intro cs
    simp [layoutList, csrList, csrData, List.length_flatMap]
  rw [key, key, List.length_set]
  congr 2
  refine List.map_congr_left fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    by_cases hi : j < bs.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set, hi, ← hl]
      simp [List.getD_eq_getElem?_getD] at hl; simp [hl, hi]
    · rw [List.set_eq_of_length_le (by omega)]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hj]

theorem HierConcrete.sections_withGlob (x : HierConcrete) (S : Finset ℕ) :
    (x.withGlob S).sections =
      x.sections.set 14 (bitsList x.H.A.C.numTerm fun t => decide (t ∈ S)) := by
  simp only [HierConcrete.sections, HierConcrete.header, withGlob, HierConcrete.withSt,
    HierConcrete.n, HierConcrete.m, HierConcrete.depth]
  simp [List.set]
  all_goals (and_intros <;> rfl)

theorem HierConcrete.length_encode_withGlob (x : HierConcrete) (S : Finset ℕ) :
    (x.withGlob S).encode.length = x.encode.length := by
  show (layoutList (x.withGlob S).sections).length = (layoutList x.sections).length
  rw [x.sections_withGlob]
  exact length_layoutList_set _ (by simp [HierConcrete.sections])

/-- The members `lo, …, i - 1` that were not lost. -/
def enumOut (G : Finset ℕ) (lo i : ℕ) : List ℕ := (List.range' lo (i - lo)).filter fun v => v ∉ G

/-- The lost set after the members `lo, …, i - 1`. -/
def enumSet (G : Finset ℕ) (lo i : ℕ) : Finset ℕ := G ∪ (List.range' lo (i - lo)).toFinset

theorem range'_succ_right (lo i : ℕ) (h : lo ≤ i) :
    List.range' lo (i + 1 - lo) = List.range' lo (i - lo) ++ [i] := by
  have e : i + 1 - lo = (i - lo) + 1 := by omega
  rw [e, List.range'_concat]
  congr 2
  omega

/-- The invariant of the enumeration loop after the members `lo, …, i - 1`. -/
def EnumInv (x : HierConcrete) (b WB lo hi c0 : ℕ) (R : ℕ → ℕ) (L0 : List ℕ) (mem0 : ℕ → ℕ)
    (i : ℕ) (st : State) : Prop :=
  st.regs 20 = i ∧ (∀ r, r ≠ 20 → r ≠ 23 → r ≠ 24 → st.regs r = R r) ∧
  st.regs 23 = c0 + (enumOut x.ms.st.loss.glob lo i).length ∧
  ListAt st.mem b (x.withGlob (enumSet x.ms.st.loss.glob lo i)).encode ∧
  ListAt st.mem WB (L0 ++ enumOut x.ms.st.loss.glob lo i) ∧
  (∀ a, (a < b ∨ b + x.encode.length ≤ a) →
    (a < WB + c0 ∨ WB + c0 + (enumOut x.ms.st.loss.glob lo i).length ≤ a) → st.mem a = mem0 a)

theorem enumBody_triple {w : ℕ} {p : Program} (x : HierConcrete) {b WB lo hi c0 : ℕ}
    {R : ℕ → ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ} (hR0 : R 0 = b) (hR22 : R 22 = WB)
    (hL0 : L0.length = c0) (hhi : hi ≤ x.H.A.C.numTerm) (hblk : b + x.encode.length ≤ WB)
    (hw : WB + c0 + (hi - lo) < 2 ^ w) {i : ℕ} (hlo : lo ≤ i) (hi' : i < hi) :
    Triple w p (EnumInv x b WB lo hi c0 R L0 mem0 i) enumBody
      (normalPost fun st₁ =>
        EnumInv x b WB lo hi c0 R L0 mem0 (i + 1)
          { st₁ with regs := Function.update st₁.regs 20 (i + 1) } ∧ st₁.regs 20 = i)
      (fun _ => 120) := by
  set G := x.ms.st.loss.glob with hG
  have h25 := x.le_length_encode
  have hlen : ∀ S, (x.withGlob S).sections.length = numSec := fun _ => rfl
  have hs14 : ∀ S, (x.withGlob S).sections.getD 14 [] =
      bitsList x.H.A.C.numTerm fun t => decide (t ∈ S) := by
    intro S; simp [HierConcrete.sections, HierConcrete.withGlob, HierConcrete.withSt]; rfl
  have hbw : ∀ S, b + (x.withGlob S).encode.length < 2 ^ w := by
    intro S; rw [x.length_encode_withGlob]; omega
  have hnotin : i ∉ (List.range' lo (i - lo)) := by simp [List.mem_range']; omega
  have hset1 : enumSet G lo (i + 1) = insert i (enumSet G lo i) := by
    unfold enumSet; rw [range'_succ_right lo i hlo]; ext v; simp
  have hout1 : enumOut G lo (i + 1) = enumOut G lo i ++ (if i ∈ G then [] else [i]) := by
    unfold enumOut; rw [range'_succ_right lo i hlo, List.filter_append]
    by_cases h : i ∈ G <;> simp [h]
  have hmemS : i ∈ enumSet G lo i ↔ i ∈ G := by
    unfold enumSet; simp [Finset.mem_union, hnotin]
  have houtle : (enumOut G lo i).length ≤ i - lo := by
    unfold enumOut; exact (List.length_filter_le _ _).trans (by simp)
  have hil : i < x.H.A.C.numTerm := by omega
  have h14 : 14 < numSec := by norm_num
  -- Step 1: read the lost bit
  have t1 : Triple w p (EnumInv x b WB lo hi c0 R L0 mem0 i)
      (.assign 24 (readSec numSec 0 14 (.reg 20)))
      (normalPost fun s => EnumInv x b WB lo hi c0 R L0 mem0 i s ∧
        s.regs 24 = if i ∈ G then 1 else 0) (fun _ => (readSec numSec 0 14 (.reg 20)).size + 1) := by
    refine Triple.assign (val := fun _ => if i ∈ G then 1 else 0) (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨h20, hR, _, hblock, _, _⟩ := hs
      have hl' : ListAt s.mem b (layoutList (x.withGlob (enumSet G lo i)).sections) := hblock
      have := eval_readSec' (w := w) hl' (hbw _) (by rw [hR 0 (by norm_num) (by norm_num)
        (by norm_num), hR0]) (i := 14) (by rw [hlen]; norm_num) (ke := .reg 20) (k := i)
        (Expr.eval_reg_of_eq h20) (by rw [hs14]; simpa using hil)
      rw [hlen, hs14, List.getD_eq_getElem _ _ (by simpa using hil)] at this
      simp only [bitsList, List.getElem_map, List.getElem_range] at this
      rw [this]
      by_cases h : i ∈ G <;> simp [h, hmemS]
    · obtain ⟨h20, hR, h23, hblock, hwl, hfr⟩ := hs
      refine ⟨⟨?_, fun r h1 h2 h3 => ?_, ?_, hblock, hwl, hfr⟩, by simp⟩
      · simpa [Function.update_apply] using h20
      · simpa [Function.update_apply, h3] using hR r h1 h2 h3
      · simpa [Function.update_apply] using h23
  -- the registers other than `24`
  let RegOK : ℕ → State → Prop := fun c s =>
    s.regs 20 = i ∧ (∀ r, r ≠ 20 → r ≠ 23 → r ≠ 24 → s.regs r = R r) ∧ s.regs 23 = c
  let Frame : ℕ → (ℕ → ℕ) → Prop := fun n m => ∀ a, (a < b ∨ b + x.encode.length ≤ a) →
    (a < WB + c0 ∨ WB + c0 + n ≤ a) → m a = mem0 a
  set S := enumSet G lo i with hS
  set out := enumOut G lo i with hout
  set cnt := c0 + out.length with hcnt
  have hwl_len : (L0 ++ out).length = cnt := by simp [hL0, hcnt]
  let Post : State → Prop := fun st₁ =>
    EnumInv x b WB lo hi c0 R L0 mem0 (i + 1)
      { st₁ with regs := Function.update st₁.regs 20 (i + 1) } ∧ st₁.regs 20 = i
  have post_of : ∀ s : State, RegOK cnt s ∨ RegOK (cnt + 1) s →
      s.regs 23 = c0 + (enumOut G lo (i + 1)).length →
      ListAt s.mem b (x.withGlob (enumSet G lo (i + 1))).encode →
      ListAt s.mem WB (L0 ++ enumOut G lo (i + 1)) →
      Frame (enumOut G lo (i + 1)).length s.mem → Post s := by
    intro s hreg h23 hb' hwl' hfr
    have h20 : s.regs 20 = i := by rcases hreg with h | h <;> exact h.1
    have hR' : ∀ r, r ≠ 20 → r ≠ 23 → r ≠ 24 → s.regs r = R r := by
      rcases hreg with h | h <;> exact h.2.1
    refine ⟨⟨by simp, fun r h1 h2 h3 => ?_, ?_, hb', hwl', ?_⟩, h20⟩
    · simpa [Function.update_apply, h1] using hR' r h1 h2 h3
    · simpa [Function.update_apply] using h23
    · intro a h1 h2; exact hfr a h1 h2
  have t2 : Triple w p (fun s => EnumInv x b WB lo hi c0 R L0 mem0 i s ∧
        s.regs 24 = if i ∈ G then 1 else 0)
      (.cond (.reg 24) .nop
        (.seq (.store (secAddr numSec 0 14 (.reg 20)) (.const 1))
          (.seq (.store (.bin .add (.reg 22) (.reg 23)) (.reg 20))
            (.assign 23 (.bin .add (.reg 23) (.const 1))))))
      (normalPost Post) (fun _ => 60) := by
    by_cases hiG : i ∈ G
    · refine (Triple.cond (val := fun s => s.regs 24) (fun _ _ => Expr.eval_reg_of_eq rfl)
        (Triple.nop fun s hs => ?_) (fun s ω h => ?_) (T_f := fun _ => 0)).mono_cost
        (fun s hs => ?_)
      · obtain ⟨⟨⟨h20, hR, h23, hblock, hwl, hfr⟩, _⟩, _⟩ := hs
        have hS1 : enumSet G lo (i + 1) = S := by
          rw [hset1]; exact Finset.insert_eq_of_mem (hmemS.mpr hiG)
        have hO1 : enumOut G lo (i + 1) = out := by rw [hout1]; simp [hiG]
        exact post_of s (Or.inl ⟨h20, hR, h23⟩) (by rw [hO1]; exact h23) (by rw [hS1]; exact hblock)
          (by rw [hO1]; exact hwl) (by show Frame _ _; rw [hO1]; exact hfr)
      · obtain ⟨⟨_, h24⟩, hz⟩ := h
        simp [h24, hiG] at hz
      · have : s.regs 24 = 1 := by simp [hs.2, hiG]
        simp [this, Expr.size]
    · refine (Triple.cond (val := fun s => s.regs 24) (fun _ _ => Expr.eval_reg_of_eq rfl)
        (fun s ω h => ?_) (T_t := fun _ => 0) (T_f := fun _ => 40) ?_).mono_cost (fun s hs => ?_)
      · obtain ⟨⟨_, h24⟩, hz⟩ := h
        simp [h24, hiG] at hz
      · -- not lost: set the bit, append to the work list, count it
        have hS1 : enumSet G lo (i + 1) = insert i S := hset1
        have hO1 : enumOut G lo (i + 1) = out ++ [i] := by rw [hout1]; simp [hiG]
        let y := x.withGlob S
        have hyl : y.sections.length = numSec := rfl
        have hy14 : i < (y.sections.getD 14 []).length := by rw [hs14]; simpa using hil
        have hsecy : (x.withGlob (insert i S)).sections =
            y.sections.set 14 ((y.sections.getD 14 []).set i 1) := y.sections_setGlob i
        let P1 : State → Prop := fun s => RegOK cnt s ∧
          ListAt s.mem b (x.withGlob (insert i S)).encode ∧ ListAt s.mem WB (L0 ++ out) ∧
          Frame out.length s.mem
        let P2 : State → Prop := fun s => RegOK cnt s ∧
          ListAt s.mem b (x.withGlob (insert i S)).encode ∧ ListAt s.mem WB (L0 ++ out ++ [i]) ∧
          Frame (out.length + 1) s.mem
        have s1 : Triple w p (fun s => (EnumInv x b WB lo hi c0 R L0 mem0 i s ∧
              s.regs 24 = if i ∈ G then 1 else 0) ∧ s.regs 24 = 0)
            (.store (secAddr numSec 0 14 (.reg 20)) (.const 1)) (normalPost P1)
            (fun _ => (secAddr numSec 0 14 (.reg 20)).size + (Expr.const 1).size + 1) := by
          refine Triple.store (addr := fun s => b + (numSec + 1) + s.mem (b + 14) + i)
            (val := fun _ => 1) (fun s hs => ?_) (fun s hs => Expr.eval_const (by omega))
            (fun s hs => ?_)
          · obtain ⟨⟨⟨h20, hR, _, hblock, _, _⟩, _⟩, _⟩ := hs
            have hl' : ListAt s.mem b (layoutList y.sections) := hblock
            have := eval_secAddr (w := w) hl' (hbw S) (r := 0)
              (by rw [hR 0 (by norm_num) (by norm_num) (by norm_num), hR0]) (i := 14)
              (by rw [hyl]; norm_num) (ke := .reg 20) (k := i) (Expr.eval_reg_of_eq h20) hy14
            rw [hyl] at this
            exact this
          · obtain ⟨⟨⟨h20, hR, h23, hblock, hwl, hfr⟩, _⟩, _⟩ := hs
            have hl' : ListAt s.mem b (layoutList y.sections) := hblock
            have hoff := mem_secOffset hl' (i := 14) (by rw [hyl]; norm_num)
            have hlt := addr_lt_length (bs := y.sections) (i := 14) (by rw [hyl]; norm_num) hy14
            rw [hyl] at hlt
            have hyenc : (layoutList y.sections).length = x.encode.length :=
              x.length_encode_withGlob S
            have hA : b + (numSec + 1) + s.mem (b + 14) + i < b + x.encode.length := by
              rw [hoff]; omega
            have hnew := listAt_layout_write hl' (i := 14) (by rw [hyl]; norm_num) hy14 1
            rw [hyl] at hnew
            refine ⟨⟨h20, hR, h23⟩, ?_, ?_, ?_⟩
            · show ListAt _ b (layoutList (x.withGlob (insert i S)).sections)
              rw [hsecy]; exact hnew
            · refine listAt_congr (fun k hk => ?_) hwl
              show _ = Function.update s.mem _ _ _
              exact (Function.update_of_ne (by omega) _ _).symm
            · intro a h1 h2
              show Function.update _ _ _ a = _
              rw [Function.update_of_ne (by omega)]; exact hfr a h1 h2
        have s2 : Triple w p P1 (.store (.bin .add (.reg 22) (.reg 23)) (.reg 20)) (normalPost P2)
            (fun _ => (Expr.bin .add (.reg 22) (.reg 23)).size + (Expr.reg 20).size + 1) := by
          refine Triple.store (addr := fun _ => WB + cnt) (val := fun _ => i) (fun s hs => ?_)
            (fun s hs => Expr.eval_reg_of_eq hs.1.1) (fun s hs => ?_)
          · obtain ⟨⟨_, hR, h23⟩, _⟩ := hs
            exact Expr.eval_add (Expr.eval_reg_of_eq (by rw [hR 22 (by norm_num) (by norm_num)
              (by norm_num), hR22])) (Expr.eval_reg_of_eq h23) (by omega)
          · obtain ⟨hreg, hblock, hwl, hfr⟩ := hs
            refine ⟨hreg, ?_, ?_, ?_⟩
            · refine listAt_congr (fun k hk => ?_) hblock
              rw [x.length_encode_withGlob] at hk
              show _ = Function.update s.mem _ _ _
              exact (Function.update_of_ne (by omega) _ _).symm
            · have := listAt_append_one hwl i
              rw [hwl_len] at this
              exact this
            · intro a h1 h2
              show Function.update _ _ _ a = _
              rw [Function.update_of_ne (by omega)]
              exact hfr a h1 (by omega)
        have s3 : Triple w p P2 (.assign 23 (.bin .add (.reg 23) (.const 1))) (normalPost Post)
            (fun _ => (Expr.bin .add (.reg 23) (.const 1)).size + 1) := by
          refine Triple.assign (val := fun _ => cnt + 1)
            (fun s hs => Expr.eval_add (Expr.eval_reg_of_eq hs.1.2.2) (Expr.eval_const (by omega))
              (by omega)) (fun s hs => ?_)
          obtain ⟨⟨h20, hR, _⟩, hblock, hwl, hfr⟩ := hs
          refine post_of _ (Or.inr ⟨by simpa [Function.update_apply] using h20,
            fun r h1 h2 h3 => by simpa [Function.update_apply, h2] using hR r h1 h2 h3,
            by simp⟩) (by simp [hO1, hcnt]; omega) (by rw [hS1]; exact hblock)
            (by rw [hO1, ← List.append_assoc]; exact hwl)
            (by show Frame _ _; rw [hO1, List.length_append, List.length_singleton]; exact hfr)
        exact (Triple.seq_normal_const s1 (Triple.seq_normal_const s2 s3)).mono_cost
          (fun _ _ => by simp [secAddr, Expr.size])
      · have : s.regs 24 = 0 := by simp [hs.2, hiG]
        simp [this, Expr.size]
  refine (Triple.seq_normal t1 t2 (fun _ _ _ _ => ?_)).strengthen_post fun o s h => h
  simp [readSec, secAddr, Expr.size]

theorem HierConcrete.withGlob_self (x : HierConcrete) : x.withGlob x.ms.st.loss.glob = x := rfl

/-- **The enumeration loop.** With the group `X` in register `14`, its size `sz` in register
`15`, the end `X · sz + sz` in register `21`, the work list at `WB` with `c0` words in register
`23`, the loop marks the members lost and appends those not lost before. -/
theorem enumLoop_triple {w : ℕ} {p : Program} (x : HierConcrete) {b WB X sz c0 : ℕ}
    {R : ℕ → ℕ} {L0 : List ℕ} {mem0 : ℕ → ℕ} (hR0 : R 0 = b) (hR14 : R 14 = X)
    (hR15 : R 15 = sz) (hR21 : R 21 = X * sz + sz) (hR22 : R 22 = WB) (hR23 : R 23 = c0)
    (hL0 : L0.length = c0) (hhi : X * sz + sz ≤ x.H.A.C.numTerm)
    (hblk : b + x.encode.length ≤ WB) (hw : WB + c0 + sz < 2 ^ w)
    (hhw : X * sz + sz < 2 ^ w) :
    Triple w p (fun st => st.regs = R ∧ ListAt st.mem b x.encode ∧ ListAt st.mem WB L0 ∧
        st.mem = mem0)
      (forRange 20 (.bin .mul (.reg 14) (.reg 15)) (.reg 21) enumBody)
      (normalPost (EnumInv x b WB (X * sz) (X * sz + sz) c0 R L0 mem0 (X * sz + sz)))
      (fun _ => 130 * sz + 20) := by
  have h25 := x.le_length_encode
  have hw' : WB + c0 + (X * sz + sz - X * sz) < 2 ^ w := by
    rw [Nat.add_sub_cancel_left]; exact hw
  refine (Triple.forRange_le (fun _ => 120) (X * sz) (X * sz + sz) (by omega) (by omega)
    (fun _ => hhw) (fun st hP => ⟨?_, ?_⟩) (fun i st _ _ h => h.1)
    (fun i st _ _ h => Expr.eval_reg_of_eq (by rw [h.2.1 21 (by norm_num) (by norm_num)
      (by norm_num), hR21]))
    (fun i hlo hlt => enumBody_triple x hR0 hR22 hL0 hhi hblk hw' hlo hlt)).mono_cost ?_
  · obtain ⟨hr, _, _, _⟩ := hP
    exact Expr.eval_mul (Expr.eval_reg_of_eq (by rw [hr, hR14]))
      (Expr.eval_reg_of_eq (by rw [hr, hR15])) (by omega)
  · obtain ⟨hr, hblock, hwl, hm⟩ := hP
    refine ⟨by simp, fun r h1 _ _ => ?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_apply, h1, hr]
    · simp [Function.update_apply, hr, hR23, enumOut]
    · simp only [enumSet, Nat.sub_self, List.range'_zero, List.toFinset_nil, Finset.union_empty,
        HierConcrete.withGlob_self]
      exact hblock
    · simpa [enumOut] using hwl
    · intro a _ _; rw [← hm]
  · intro _ _
    have := rangeCost_le_mul (f := fun _ => 120) (lo := X * sz) (hi := X * sz + sz)
      (c := 120) (fun _ _ _ => le_refl _)
    simp only [Nat.add_sub_cancel_left] at this ⊢
    simp [Expr.size]
    omega

/-- After the whole group, the lost set and the work list are those of `enumerate`. -/
theorem enumerate_eq_enum (st : LossState) (x b j X : ℕ) :
    (enumerate st (memberList x b j X)).1.glob =
        enumSet st.glob (X * groupSize x b j) (X * groupSize x b j + groupSize x b j) ∧
      (enumerate st (memberList x b j X)).2 =
        enumOut st.glob (X * groupSize x b j) (X * groupSize x b j + groupSize x b j) := by
  simp [enumerate, enumSet, enumOut, memberList]

end MinCostFlow.HierPaths

end
