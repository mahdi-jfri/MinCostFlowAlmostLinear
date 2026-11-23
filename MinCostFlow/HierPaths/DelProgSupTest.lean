module

public import MinCostFlow.HierPaths.DelProgPairTest

/-!
# The validity test of the support cursors

Entry `i` of the support array of a vertex `w` is valid when it is live
(`StaticArrays.supValid`): a terminal entry when its terminal survives, a walk entry when its
connector is eligible. In memory, entry `i` is three words of list `w` of section 9, starting at
word `3 i` (`entryWords`): the tag (`0` for a terminal, `1` for a walk), then the terminal or the
connector. A terminal survives when its lost bit (section 14) is clear, and by the invariant
(`inelig_eq`) a connector is eligible when its ineligibility bit (section 15) is clear.

`supTestStmt` reads the tag and the number, then returns `1` minus the right bit. With
`supTest_triple`, `supAdvance_triple` moves a support cursor.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Spanner MinCostFlow.Cited

theorem getD_flatMap_three {α : Type} (g : α → List ℕ) (hg : ∀ a, (g a).length = 3) :
    ∀ (l : List α) {i : ℕ} (hi : i < l.length) {k : ℕ}, k < 3 →
      (l.flatMap g).getD (3 * i + k) 0 = (g l[i]).getD k 0
  | [], i, hi, _, _ => by simp at hi
  | a :: l, 0, _, k, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
    rw [List.getD_append _ _ _ _ (by rw [hg]; exact hk)]
  | a :: l, i + 1, hi, k, hk => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    have e : 3 * (i + 1) + k = (g a).length + (3 * i + k) := by rw [hg]; ring
    rw [e, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
    exact getD_flatMap_three g hg l (by simp at hi; omega) hk

theorem length_entryWords (a : SupportEntry) : (entryWords a).length = 3 := by
  cases a <;> rfl

/-- The address of word `3 · cur + k` of the support array of the vertex in register `rw`. -/
def supWordIdx (rw rc k : ℕ) : Expr :=
  .bin .add (.bin .add (readSec numSec 0 0 (.const 0)) (.const 1))
    (.bin .add (readSec numSec 0 9 (.reg rw))
      (.bin .add (.bin .mul (.const 3) (.reg rc)) (.const k)))

/-- Read the tag and the number of entry `cur`, then set `rv` to `1` minus the bit. -/
def supTestStmt (rw rc rtag rid rv : ℕ) : Stmt :=
  .seq (.assign rtag (readSec numSec 0 9 (supWordIdx rw rc 0)))
    (.seq (.assign rid (readSec numSec 0 9 (supWordIdx rw rc 1)))
      (.cond (.reg rtag)
        (.assign rv (.bin .sub (.const 1) (readSec numSec 0 15 (.reg rid))))
        (.assign rv (.bin .sub (.const 1) (readSec numSec 0 14 (.reg rid))))))

theorem supTestStmt_noRand (rw rc rtag rid rv : ℕ) : (supTestStmt rw rc rtag rid rv).NoRand := by
  simp [supTestStmt, Stmt.NoRand]

/-- **The support test.** -/
theorem supTest_triple {w : ℕ} {p : Program} (x : HierConcrete) {b v : ℕ}
    {rw rc rgo rtag rid rv : ℕ} (h0t : rtag ≠ 0) (h0i : rid ≠ 0) (h0v : rv ≠ 0)
    (hwt : rtag ≠ rw) (hwi : rid ≠ rw) (hct : rtag ≠ rc) (hci : rid ≠ rc) (hcv : rv ≠ rc)
    (hgt : rtag ≠ rgo) (hgi : rid ≠ rgo) (hgv : rv ≠ rgo) (hti : rtag ≠ rid) (htv : rtag ≠ rv)
    (hiv : rid ≠ rv)
    (hv : v < x.n) (hb : b + x.encode.length < 2 ^ w)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    {F : State → Prop}
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs rw = v ∧ ListAt s.mem b x.encode)
    (hFt : ∀ s u, F s → F { s with regs := Function.update s.regs rtag u })
    (hFi : ∀ s u, F s → F { s with regs := Function.update s.regs rid u })
    (hFv : ∀ s u, F s → F { s with regs := Function.update s.regs rv u })
    (c : ℕ) (hc : c < (x.H.A.C.supportArray v).length) :
    Triple w p (fun s => F s ∧ s.regs rc = c ∧ s.regs rgo = 1) (supTestStmt rw rc rtag rid rv)
      (normalPost fun s' => F s' ∧ s'.regs rc = c ∧ s'.regs rgo = 1 ∧
        s'.regs rv = if x.H.A.supValid (x.H.A.surv x.ms.st) v c then 1 else 0)
      (fun _ => 250) := by
  have hlen : x.sections.length = numSec := rfl
  have henc : 25 ≤ x.encode.length := by
    simp [HierConcrete.encode, layoutList, csrList]
  have hs9 : x.sections.getD 9 [] =
      csrList x.n fun u => (x.H.A.C.supportArray u).flatMap entryWords := by
    simp [HierConcrete.sections]
  have hs14 : x.sections.getD 14 [] =
      bitsList x.H.A.C.numTerm fun t => decide (t ∈ x.ms.st.loss.glob) := by
    simp [HierConcrete.sections]
  have hs15 : x.sections.getD 15 [] =
      bitsList x.H.A.C.numConn fun c => decide (c ∈ x.ms.st.inelig) := by
    simp [HierConcrete.sections]
  have hs0 : x.sections.getD 0 [] = x.header := by simp [HierConcrete.sections]
  have hl0 : 0 < x.sections.length := by rw [hlen]; norm_num
  have hl9 : 9 < x.sections.length := by rw [hlen]; norm_num
  have hl14 : 14 < x.sections.length := by rw [hlen]; norm_num
  have hl15 : 15 < x.sections.length := by rw [hlen]; norm_num
  set f := fun u => (x.H.A.C.supportArray u).flatMap entryWords with hf
  set off := ((List.range v).map fun i => (f i).length).sum with hoff
  set ent := (x.H.A.C.supportArray v)[c] with hent
  have hflen : (f v).length = 3 * (x.H.A.C.supportArray v).length := by
    simp only [hf, List.length_flatMap, length_entryWords]
    simp [mul_comm]
  have hvl : v < (x.sections.getD 9 []).length := by rw [hs9]; simp [csrList]; omega
  have hword : ∀ k < 3, (x.sections.getD 9 []).getD (x.n + 1 + (off + (3 * c + k))) 0 =
      (entryWords ent).getD k 0 := by
    intro k hk
    rw [hs9, ← Nat.add_assoc, csrList_getD_data f hv (by rw [hflen]; omega)]
    exact getD_flatMap_three entryWords length_entryWords _ hc hk
  have hwl : ∀ k < 3, x.n + 1 + (off + (3 * c + k)) < (x.sections.getD 9 []).length := by
    intro k hk
    have := csrList_data_lt f hv (k := 3 * c + k) (by rw [hflen]; omega)
    rw [hs9]; omega
  have hww : ∀ k < 3, x.n + 1 + (off + (3 * c + k)) < 2 ^ w := by
    intro k hk
    have := lt_length_of_sec hl9 (hwl k hk)
    have h' : (layoutList x.sections).length = x.encode.length := rfl
    omega
  have hread : ∀ s, F s → s.regs rc = c → ∀ k < 3,
      (readSec numSec 0 9 (supWordIdx rw rc k)).eval w s = some ((entryWords ent).getD k 0) := by
    intro s hs hrc k hk
    obtain ⟨hr0, hrw, hl⟩ := hF s hs
    have hl' : ListAt s.mem b (layoutList x.sections) := hl
    have hn : (readSec numSec 0 0 (.const 0)).eval w s = some x.n := by
      have := eval_readSec' (w := w) hl' hb hr0 hl0 (ke := .const 0) (k := 0)
        (Expr.eval_const (by omega)) (by rw [hs0]; simp [HierConcrete.header])
      rw [hlen, hs0] at this
      simpa [HierConcrete.header] using this
    have hoffv : (readSec numSec 0 9 (.reg rw)).eval w s = some off := by
      have := eval_readSec' (w := w) hl' hb hr0 hl9 (ke := .reg rw) (k := v)
        (Expr.eval_reg_of_eq hrw) hvl
      rw [hlen, hs9, csrList_getD_offset _ hv.le] at this
      exact this
    have hkw := hww k hk
    have := eval_readSec' (w := w) hl' hb hr0 hl9 (ke := supWordIdx rw rc k)
      (k := x.n + 1 + (off + (3 * c + k)))
      (Expr.eval_add (Expr.eval_add hn (Expr.eval_const (by omega)) (by omega))
        (Expr.eval_add hoffv (Expr.eval_add (Expr.eval_bin (op := .mul)
          (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq hrc) (by show 3 * c < 2 ^ w; omega))
          (Expr.eval_const (by omega)) (by show 3 * c + k < 2 ^ w; omega))
          (by omega)) (by omega)) (hwl k hk)
    rw [hlen, hword k hk] at this
    exact this
  have hmemEnt : ent ∈ x.H.A.C.supportArray v := List.getElem_mem hc
  have hvalid : x.H.A.supValid (x.H.A.surv x.ms.st) v c = x.H.A.C.entryLive
      (x.H.A.surv x.ms.st) ent := by
    unfold StaticArrays.supValid
    rw [List.getD_eq_getElem _ _ hc]
  -- the bit read in each branch
  have hbit : ∀ s, F s → ∀ (i : ℕ) (hi : i < x.sections.length) (len : ℕ) (S : Finset ℕ),
      x.sections.getD i [] = bitsList len (fun j => decide (j ∈ S)) → ∀ u < len,
      s.regs rid = u → (Expr.bin .sub (.const 1) (readSec numSec 0 i (.reg rid))).eval w s =
        some (if u ∈ S then 0 else 1) := by
    intro s hs i hi len S hsi u hu hru
    obtain ⟨hr0, _, hl⟩ := hF s hs
    have hl' : ListAt s.mem b (layoutList x.sections) := hl
    have := eval_readSec' (w := w) hl' hb hr0 hi (ke := .reg rid) (k := u)
      (Expr.eval_reg_of_eq hru) (by rw [hsi]; simpa using hu)
    rw [hlen, hsi, List.getD_eq_getElem _ _ (by simpa using hu)] at this
    simp only [bitsList, List.getElem_map, List.getElem_range] at this
    have e := Expr.eval_bin (op := .sub) (Expr.eval_const (w := w) (st := s) (k := 1) (by omega))
      this (by simp only [BinOp.eval]; split_ifs <;> omega)
    rw [e]
    by_cases hh : u ∈ S <;> simp [BinOp.eval, hh]
  refine Triple.seq_normal
    (R := fun s1 => F s1 ∧ s1.regs rc = c ∧ s1.regs rgo = 1 ∧
      s1.regs rtag = (entryWords ent).getD 0 0)
    (Triple.assign (val := fun _ => (entryWords ent).getD 0 0)
      (fun s hs => hread s hs.1 hs.2.1 0 (by norm_num)) fun s hs => ?_)
    (Triple.seq_normal (T := fun _ => 130)
      (R := fun s1 => F s1 ∧ s1.regs rc = c ∧ s1.regs rgo = 1 ∧
        s1.regs rtag = (entryWords ent).getD 0 0 ∧ s1.regs rid = (entryWords ent).getD 1 0)
      (Triple.assign (val := fun _ => (entryWords ent).getD 1 0)
        (fun s hs => hread s hs.1 hs.2.1 1 (by norm_num)) fun s hs => ?_)
      ((Triple.cond (val := fun s => s.regs rtag) (fun _ _ => Expr.eval_reg_of_eq rfl)
        (Triple.assign (val := fun _ => if x.H.A.supValid (x.H.A.surv x.ms.st) v c then 1 else 0)
          (fun s hs => ?_) fun s hs => ?_)
        (Triple.assign (val := fun _ => if x.H.A.supValid (x.H.A.surv x.ms.st) v c then 1 else 0)
          (fun s hs => ?_) fun s hs => ?_)).mono_cost (T' := fun _ => 60) ?_) ?_) ?_
  · refine ⟨hFt _ _ hs.1, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hct)]; exact hs.2.1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgt)]; exact hs.2.2
  · obtain ⟨hF1, hc1, hg1, ht1⟩ := hs
    refine ⟨hFi _ _ hF1, ?_, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hci)]; exact hc1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgi)]; exact hg1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne hti]; exact ht1
  · -- tag 1: a walk entry
    obtain ⟨⟨hF1, _, _, ht1, hi1⟩, hne⟩ := hs
    cases hE : ent with
    | term t => rw [hE] at ht1; simp [entryWords] at ht1; exact absurd ht1 hne
    | onWalk cc pos =>
      have hcc : cc < x.H.A.C.numConn := by
        rcases (x.H.A.C.mem_supportArray).mp hmemEnt with ⟨t, _, _, h⟩ | ⟨c', hc', _, _, h⟩
        · rw [hE] at h; cases h
        · rw [hE] at h; cases h; exact hc'
      rw [hE] at hi1
      rw [hbit s hF1 15 hl15 _ _ hs15 cc hcc (by simpa [entryWords] using hi1), hvalid, hE]
      simp only [ConnectorSystem.entryLive]
      rw [hinel]
      by_cases hh : x.H.A.C.Eligible (x.H.A.surv x.ms.st) cc <;> simp [hh, hcc]
  · obtain ⟨⟨hF1, hc1, hg1, _, _⟩, _⟩ := hs
    refine ⟨hFv _ _ hF1, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hcv)]; exact hc1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgv)]; exact hg1
  · -- tag 0: a terminal entry
    obtain ⟨⟨hF1, _, _, ht1, hi1⟩, hz⟩ := hs
    cases hE : ent with
    | onWalk cc pos => rw [hE] at ht1; simp [entryWords] at ht1; exact absurd ht1 (by omega)
    | term t =>
      have htl : t < x.H.A.C.numTerm := by
        rcases (x.H.A.C.mem_supportArray).mp hmemEnt with ⟨t', ht', _, h⟩ | ⟨c', _, _, _, h⟩
        · rw [hE] at h; cases h; exact ht'
        · rw [hE] at h; cases h
      rw [hE] at hi1
      rw [hbit s hF1 14 hl14 _ _ hs14 t htl (by simpa [entryWords] using hi1), hvalid, hE]
      simp only [ConnectorSystem.entryLive, StaticArrays.mem_surv]
      by_cases hh : t ∈ x.ms.st.loss.glob <;> simp [hh, htl]
  · obtain ⟨⟨hF1, hc1, hg1, _, _⟩, _⟩ := hs
    refine ⟨hFv _ _ hF1, ?_, ?_, by simp⟩
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hcv)]; exact hc1
    · show Function.update _ _ _ _ = _; rw [Function.update_of_ne (Ne.symm hgv)]; exact hg1
  · intro _ _
    split_ifs <;> simp [readSec, secAddr, supWordIdx, Expr.size]
  · intro _ _ _ _
    simp [readSec, secAddr, supWordIdx, Expr.size]
  · intro _ _ _ _
    simp [readSec, secAddr, supWordIdx, Expr.size]

/-- **Moving a support cursor.** With the length of the support array of `v` in register `rN`,
the loop moves the cursor in register `rc` from `c₀` to the next live entry. -/
theorem supAdvance_triple {w : ℕ} {p : Program} (x : HierConcrete) {b v : ℕ}
    {rw rc rN rgo rtag rid rv : ℕ} (h0t : rtag ≠ 0) (h0i : rid ≠ 0) (h0v : rv ≠ 0)
    (hwt : rtag ≠ rw) (hwi : rid ≠ rw) (hct : rtag ≠ rc) (hci : rid ≠ rc) (hcv : rv ≠ rc)
    (hgt : rtag ≠ rgo) (hgi : rid ≠ rgo) (hgv : rv ≠ rgo) (hti : rtag ≠ rid) (htv : rtag ≠ rv)
    (hiv : rid ≠ rv) (hrc : rc ≠ rgo) (hrN : rN ≠ rgo) (hrNc : rN ≠ rc)
    (hv : v < x.n) (hb : b + x.encode.length < 2 ^ w)
    (hw : (x.H.A.C.supportArray v).length + 1 < 2 ^ w)
    (hinel : x.ms.st.inelig = (Finset.range x.H.A.C.numConn).filter fun c =>
      ¬ x.H.A.C.Eligible (x.H.A.surv x.ms.st) c)
    {F : State → Prop}
    (hF : ∀ s, F s → s.regs 0 = b ∧ s.regs rw = v ∧ ListAt s.mem b x.encode)
    (hFN : ∀ s, F s → s.regs rN = (x.H.A.C.supportArray v).length)
    (hFt : ∀ s u, F s → F { s with regs := Function.update s.regs rtag u })
    (hFi : ∀ s u, F s → F { s with regs := Function.update s.regs rid u })
    (hFv : ∀ s u, F s → F { s with regs := Function.update s.regs rv u })
    (hFc : ∀ s u, F s → F { s with regs := Function.update s.regs rc u })
    (hFg : ∀ s u, F s → F { s with regs := Function.update s.regs rgo u })
    {c₀ : ℕ} (hc₀ : c₀ ≤ (x.H.A.C.supportArray v).length) :
    Triple w p (fun s => F s ∧ s.regs rc = c₀)
      (advanceStmt (supTestStmt rw rc rtag rid rv) rc rN rgo rv)
      (normalPost fun s' => F s' ∧ s'.regs rc =
        advance (x.H.A.supValid (x.H.A.surv x.ms.st) v) (x.H.A.C.supportArray v).length c₀)
      (fun _ => (advance (x.H.A.supValid (x.H.A.surv x.ms.st) v)
        (x.H.A.C.supportArray v).length c₀ - c₀ + 1) * (250 + 30) + 6) :=
  advanceStmt_triple hrc hrN hrNc hgv hw hFN hFc hFg
    (fun c hc => supTest_triple x h0t h0i h0v hwt hwi hct hci hcv hgt hgi hgv hti htv hiv hv hb
      hinel hF hFt hFi hFv c hc) hc₀

end MinCostFlow.HierPaths

end
