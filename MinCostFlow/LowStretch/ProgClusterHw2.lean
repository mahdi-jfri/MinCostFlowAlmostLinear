module

public import MinCostFlow.LowStretch.ProgClusterHw

/-!
# A highway split into light walks and steps

`hwB` (`ProgClusterHw`) builds a highway from chosen light walks. The special petal must use the
highway of the cluster itself, whose light walks are given. `HwDec e st hw` says that `hw` is a
light walk from `e` to the first step, the pair of the step, a light walk to the next step, and so
on, ending with a light walk to the center. The lemmas of `ProgClusterHw` hold for every such
`hw` (`HwDec.walk`, `HwDec.steps`, `HwDec.index`, `HwDec.highway`), and `hwB` is one of them
(`StOk.hwDec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace Cl

variable (G : PG) (c : Cl)

/-- `hw` is split into light walks and the steps `st`, from `e`. -/
inductive HwDec : ℕ → List (ℕ × ℕ × ℕ) → List ℕ → Prop
  | nil {e : ℕ} {l : List ℕ} : G.IsWalk ↑c.X (c.light G) e c.x0 l → HwDec e [] l
  | cons {e : ℕ} {s : ℕ × ℕ × ℕ} {st : List (ℕ × ℕ × ℕ)} {l hw : List ℕ} :
      G.IsWalk ↑c.X (c.light G) e s.2.1 l → G.Joins s.1 s.2.1 s.2.2 → s.2.2 ∈ c.X →
      c.d G c.x0 s.2.1 = c.d G c.x0 s.2.2 + c.len G s.1 → HwDec s.2.2 st hw →
      HwDec e (s :: st) (l ++ s.1 :: hw)

variable {G c}

theorem StOk.hwDec {e : ℕ} {st : List (ℕ × ℕ × ℕ)} (h : c.StOk G e st) :
    c.HwDec G e st (c.hwB G e st) := by
  induction h with
  | nil hl => exact .nil (lw_walk hl)
  | cons hl hj hb hd _ ih => exact .cons (lw_walk hl) hj hb hd ih

theorem HwDec.stOk {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} (h : c.HwDec G e st hw) :
    c.StOk G e st := by
  induction h with
  | nil hl => exact .nil ⟨_, hl⟩
  | cons hl hj hb hd _ ih => exact .cons ⟨_, hl⟩ hj hb hd ih

theorem HwDec.walk {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} (h : c.HwDec G e st hw) :
    G.IsWalk ↑c.X Set.univ e c.x0 hw := by
  induction h with
  | nil hl => exact hl.mono le_rfl (Set.subset_univ _)
  | cons hl hj hb _ _ ih =>
    exact (hl.mono le_rfl (Set.subset_univ _)).append (.cons hl.end_mem (Set.mem_univ _) hj ih)

/-- **Each step of the highway** keeps the distance minus the length, and either joins two
light-joined vertices or is one of the steps, with its ends. -/
theorem HwDec.steps (hc : c.Conn G) {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
    (h : c.HwDec G e st hw) {i : ℕ} (hi : i < hw.length) :
    c.d G c.x0 ((G.vtx e hw).getD i 0) =
        c.d G c.x0 ((G.vtx e hw).getD (i + 1) 0) + c.len G (hw.getD i 0) ∧
      (c.LConn G ((G.vtx e hw).getD i 0) ((G.vtx e hw).getD (i + 1) 0) ∨
        (hw.getD i 0, (G.vtx e hw).getD i 0, (G.vtx e hw).getD (i + 1) 0) ∈ st) := by
  induction h generalizing i with
  | nil hl =>
    have := light_steps hc hl (i := i) hi
    exact ⟨this.1, Or.inl this.2⟩
  | @cons e s st l hw hw0 hj hb hd hst ih =>
    have hend : G.wend e l = s.2.1 := hw0.wend_eq
    rcases Nat.lt_or_ge i l.length with h1 | h1
    · rw [PG.vtx_append_getD_le _ _ _ (by omega), PG.vtx_append_getD_le _ _ _ (by omega),
        List.getD_append _ _ _ _ h1]
      have := light_steps hc hw0 h1
      exact ⟨this.1, Or.inl this.2⟩
    · obtain ⟨k, rfl⟩ : ∃ k, i = l.length + k := ⟨i - l.length, by omega⟩
      rw [PG.vtx_append_getD, show l.length + k + 1 = l.length + (k + 1) by omega,
        PG.vtx_append_getD, hend, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      cases k with
      | zero =>
        simp only [PG.vtx, List.getD_cons_zero, List.getD_cons_succ, hj.other_eq,
          PG.vtx_getD_zero]
        exact ⟨hd, Or.inr List.mem_cons_self⟩
      | succ k =>
        simp only [PG.vtx, List.getD_cons_succ, hj.other_eq]
        simp only [List.length_append, List.length_cons] at hi
        obtain ⟨h2, h3⟩ := ih (i := k) (by omega)
        refine ⟨h2, ?_⟩
        rcases h3 with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (List.mem_cons_of_mem _ h3)

/-- **Each step is a step of the highway**, with its ends. -/
theorem HwDec.index {e : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ} (h : c.HwDec G e st hw)
    {s : ℕ × ℕ × ℕ} (hs : s ∈ st) : ∃ i < hw.length, hw.getD i 0 = s.1 ∧
      (G.vtx e hw).getD i 0 = s.2.1 ∧ (G.vtx e hw).getD (i + 1) 0 = s.2.2 := by
  induction h with
  | nil _ => simp at hs
  | @cons e s' st l hw hw0 hj hb hd hst ih =>
    have hend : G.wend e l = s'.2.1 := hw0.wend_eq
    have key : ∀ k, k < (s'.1 :: hw).length →
        (l ++ s'.1 :: hw).getD (l.length + k) 0 = (s'.1 :: hw).getD k 0 ∧
          (G.vtx e (l ++ s'.1 :: hw)).getD (l.length + k) 0 =
            (G.vtx s'.2.1 (s'.1 :: hw)).getD k 0 ∧
          (G.vtx e (l ++ s'.1 :: hw)).getD (l.length + k + 1) 0 =
            (G.vtx s'.2.1 (s'.1 :: hw)).getD (k + 1) 0 := by
      intro k _
      refine ⟨List.getD_append_right _ _ _ _ (by omega) |>.trans (by rw [Nat.add_sub_cancel_left]),
        by rw [PG.vtx_append_getD, hend], ?_⟩
      rw [show l.length + k + 1 = l.length + (k + 1) by omega, PG.vtx_append_getD, hend]
    rcases List.mem_cons.mp hs with rfl | hs'
    · refine ⟨l.length, by simp, ?_⟩
      obtain ⟨k1, k2, k3⟩ := key 0 (by simp)
      rw [Nat.add_zero] at k1 k2 k3
      rw [k1, k2, k3]
      simp only [PG.vtx, List.getD_cons_zero, List.getD_cons_succ, hj.other_eq,
        PG.vtx_getD_zero]
      simp
    · obtain ⟨i, hi, e1, e2, e3⟩ := ih hs'
      refine ⟨l.length + (i + 1), by simp; omega, ?_⟩
      obtain ⟨k1, k2, k3⟩ := key (i + 1) (by simp; omega)
      rw [k1, k2, k3]
      simp only [PG.vtx, List.getD_cons_succ, hj.other_eq]
      exact ⟨e1, e2, e3⟩

theorem HwDec.highway (hc : c.Conn G) {t : ℕ} {st : List (ℕ × ℕ × ℕ)} {hw : List ℕ}
    (h : c.HwDec G t st hw) : c.IsHighway G t hw :=
  ⟨h.walk, fun i hi => (h.steps hc hi).1⟩

end Cl

end MinCostFlow.LowStretch
