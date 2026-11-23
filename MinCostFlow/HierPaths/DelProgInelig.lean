module

public import MinCostFlow.HierPaths.DeleteStep
public import MinCostFlow.HierPaths.DelProgCsr

/-!
# Collecting newly ineligible connectors

The connector pass scans the incident lists of the newly lost terminals. It sets each
connector's ineligible bit on the first visit and records that connector for cursor refresh.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Read the incident connector interval of the terminal in register `28`. -/
def delTermSetup : Stmt := delCsrSetup 7 28 29 30 (readHdr 2)

/-- The interval in section 7 contains the terminal's incident connectors. -/
theorem delTermSetup_triple {w : ℕ} {p : Program} (x : HierConcrete) {b t : ℕ}
    {R : ℕ → ℕ} {M : (ℕ → ℕ) → Prop} (hR0 : R 0 = b) (hRt : R 28 = t)
    (ht : t < x.H.A.C.numTerm) (hM : ∀ mem, M mem → ListAt mem b x.encode)
    (hb : b + x.encode.length < 2 ^ w) :
    Triple w p (fun s => s.regs = R ∧ M s.mem) delTermSetup
      (normalPost fun s => s.regs = Function.update
        (Function.update R 29 (delCsrStart x.H.A.C.numTerm x.H.A.termConns t))
        (30 : ℕ) (delCsrStart x.H.A.C.numTerm x.H.A.termConns t +
          (x.H.A.termConns t).length) ∧ M s.mem)
      (fun _ => 80) := by
  rw [← delCsrStart_succ]
  unfold delTermSetup
  refine (delCsrSetup_triple (by norm_num)
    (by simp [HierConcrete.sections]) ht hR0 hRt (by decide) (by decide) hM hb ?_).mono_cost ?_
  · intro s hm h0
    simpa [HierConcrete.header] using x.eval_readHdr hb h0 (hM _ hm) (k := 2) (by norm_num)
  · intro s hs
    decide

/-- The first-visit order when the program marks the connectors in a list. -/
def delCollect (seen : Finset ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: cs =>
    if c ∈ seen then delCollect seen cs else c :: delCollect (insert c seen) cs

theorem mem_delCollect {seen : Finset ℕ} {cs : List ℕ} {c : ℕ} :
    c ∈ delCollect seen cs ↔ c ∈ cs ∧ c ∉ seen := by
  induction cs generalizing seen c with
  | nil => simp [delCollect]
  | cons i cs ih =>
    by_cases hi : i ∈ seen <;> by_cases hc : c = i <;>
      simp [delCollect, hi, hc, ih, Finset.mem_insert]

theorem nodup_delCollect (seen : Finset ℕ) (cs : List ℕ) : (delCollect seen cs).Nodup := by
  induction cs generalizing seen with
  | nil => simp [delCollect]
  | cons i cs ih =>
    by_cases hi : i ∈ seen
    · simpa [delCollect, hi] using ih seen
    · simp [delCollect, hi, List.nodup_cons, mem_delCollect, ih]

/-- A scan of a prefix marks all its entries before scanning the suffix. -/
theorem delCollect_append (seen : Finset ℕ) (xs ys : List ℕ) :
    delCollect seen (xs ++ ys) =
      delCollect seen xs ++ delCollect (seen ∪ xs.toFinset) ys := by
  induction xs generalizing seen with
  | nil => simp [delCollect]
  | cons c cs ih =>
    simp only [List.cons_append, delCollect, List.toFinset_cons]
    by_cases hc : c ∈ seen
    · have he : seen ∪ insert c cs.toFinset = seen ∪ cs.toFinset := by
        ext k
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl hc
          · exact Or.inr h
        · tauto
      simp only [ite_eq_left hc, ih, he]
    · have he : insert c seen ∪ cs.toFinset = seen ∪ insert c cs.toFinset := by
        ext k
        simp only [Finset.mem_union, Finset.mem_insert]
        tauto
      simp only [ite_eq_right hc, List.cons_append, ih, he]

/-- The first-visit pass selects exactly the connectors selected by the model's deduplication. -/
theorem delCollect_newInelig (A : StaticArrays) (st : DelState) (e : ℕ) :
    (delCollect st.inelig ((A.newLost st e).flatMap A.termConns)).toFinset =
      (A.newInelig st e).toFinset := by
  ext c
  simp [StaticArrays.newInelig, mem_delCollect]

end MinCostFlow.HierPaths

end
