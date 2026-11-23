module

public import MinCostFlow.HierPaths.InitProgBucketModel

/-!
# Gathering payloads in sorted order

A list of record numbers determines which word to copy from the payload
table. Each record number and payload is read once.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Arguments are the record indices, payload table, number of indices and destination. -/
def initBucketGather : Stmt :=
  forRange 4 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 3) (.reg 4))
      (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 0) (.reg 4)))))) ;;
  .ret (.bin .add (.reg 3) (.reg 2))

theorem initBucketGather_noRand : initBucketGather.NoRand := by
  simp [initBucketGather, forRange, forUp, Stmt.NoRand]

/-- The output is the corresponding list of payloads. Input cells lie outside the write range. -/
def initBucketGatherContract (w : ℕ) (ord vals : List ℕ) : Contract where
  pre args mem := ∃ ix src dst, args = [ix, src, ord.length, dst] ∧
    ListAt mem ix ord ∧ ListAt mem src vals ∧ (∀ i ∈ ord, i < vals.length) ∧
    (ix + ord.length ≤ dst ∨ dst + ord.length ≤ ix) ∧
    (src + vals.length ≤ dst ∨ dst + ord.length ≤ src) ∧
    ix + ord.length < 2 ^ w ∧ src + vals.length < 2 ^ w ∧ dst + ord.length < 2 ^ w ∧ 1 < 2 ^ w
  post args mem r mem' := ∃ ix src dst, args = [ix, src, ord.length, dst] ∧
    r = dst + ord.length ∧ ListAt mem' dst (ord.map (fun i => vals.getD i 0)) ∧
    ∀ y, y < dst ∨ r ≤ y → mem' y = mem y
  cost _ _ := 25 * ord.length + 20

theorem initBucketGather_meetsContract {w f : ℕ} {ord vals : List ℕ} {p : Program}
    (hp : p.procs[f]? = some initBucketGather) :
    MeetsContract w p f (initBucketGatherContract w ord vals) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨ix, src, dst, rfl, hix, hsrc, hord, hsep1, hsep2, hwi, hws, hwd, h1⟩ := hpre
  let len := ord.length
  let initial := startState [ix, src, len, dst] mem pos
  let out := ord.map fun i => vals.getD i 0
  let R := fun (s : State) => s.regs 0 = ix ∧ s.regs 1 = src ∧ s.regs 2 = len ∧ s.regs 3 = dst
  let Inv := fun (i : ℕ) (s : State) => R s ∧ s.regs 4 = i ∧
    ∀ j, (∀ hj : j < i, s.mem (dst + j) = out.getD j 0) ∧
      (j < dst ∨ dst + i ≤ j → s.mem j = mem j)
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 4) (hi := .reg 2)
    (lo := .const 0) (P := fun s => s = initial) (Inv := Inv)
    (body := .store (.bin .add (.reg 3) (.reg 4))
      (.load (.bin .add (.reg 1) (.load (.bin .add (.reg 0) (.reg 4))))))
    13 0 len (Nat.zero_le _) h1 (fun _ => hw _ (by simp [len]))
    (fun s hs => by
      subst s
      exact ⟨Expr.eval_const (Nat.two_pow_pos w), ⟨rfl, rfl, rfl, rfl⟩, by simp,
        fun _ => ⟨fun hj => (Nat.not_lt_zero _ hj).elim, fun _ => rfl⟩⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.1.2.2.1)
    (fun i _ hi => by
      intro s ω' ⟨⟨r0, r1, r2, r3⟩, r4, hmem⟩
      let j := ord[i]
      let payload := vals.getD j 0
      have hj : j < vals.length := hord j (List.getElem_mem hi)
      have hixFr : s.mem (ix + i) = j := ((hmem _).2 (by omega)).trans (hix i hi)
      have hsFr : s.mem (src + j) = payload := by
        change s.mem (src + j) = vals.getD j 0
        rw [(hmem _).2 (by omega), List.getD_eq_getElem _ _ hj]
        exact hsrc j hj
      have hval : out.getD i 0 = payload := by
        rw [List.getD_eq_getElem _ _ (show i < out.length by simpa [out, len] using hi),
          List.getElem_map]
      refine runs_start_le ?_
      refine runs_store_le (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r4) (by omega))
        (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r1)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0)
            (Expr.eval_reg_of_eq r4) (by omega)) hixFr) (by omega)) hsFr) ?_ ?_
      · refine ⟨⟨⟨r0, r1, r2, r3⟩, by simp, fun k => ⟨?_, ?_⟩⟩, r4⟩
        · intro hk
          change Function.update s.mem (dst + i) payload (dst + k) = out.getD k 0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk' | rfl
          · exact (Function.update_of_ne (by omega) _ _).trans ((hmem k).1 hk')
          · exact (Function.update_self ..).trans hval.symm
        · intro hk
          exact (Function.update_of_ne (by omega) _ _).trans ((hmem k).2 (by omega))
      · simp [Expr.size])
  refine runs_start_le ?_
  unfold initBucketGather
  refine runs_seq_triple_le hloop rfl ?_
  intro s ⟨⟨_, _, r2, r3⟩, _, hmem⟩
  refine runs_ret_le (v := dst + len) (Expr.eval_add (Expr.eval_reg_of_eq r3)
    (Expr.eval_reg_of_eq r2) hwd) ⟨ix, src, dst, rfl, rfl, ?_, fun y hy => (hmem y).2 hy⟩ ?_
  · intro i hi
    have hi' : i < len := by simpa [out, len] using hi
    rw [← List.getD_eq_getElem _ _ hi]
    exact (hmem i).1 hi'
  · simp [initBucketGatherContract, Expr.size, len]
    omega

end MinCostFlow.HierPaths

end
