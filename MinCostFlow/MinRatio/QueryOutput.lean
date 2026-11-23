module

public import MinCostFlow.IPM.Machine.Layout
public import MinCostFlow.MinRatio.PathPayloadLayout
public import MinCostFlow.Num.Copy
public import MinCostFlow.Num.Negate
import WordRAM.Tactic

/-!
# Writing a Query answer in the original edge direction

Definition 4.5 (page 14) asks for the current flow on a named edge. Once
the edge's flow block has been located, its direction bit determines
whether Query copies the block or negates it. This procedure writes the
scalar expected by the IPM contract. It uses the numeric library for
both branches and takes linear time in the block length.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Arguments are source, direction bit, limb count, and heap. A direction
of one agrees with the original edge direction. -/
def queryOutputBody (copy negate : ℕ) : Stmt :=
  .cond (.reg 1)
    (.call 4 copy [.reg 0, .reg 2, .reg 3] ;; .ret (.reg 4))
    (.call 4 negate [.reg 0, .reg 2, .reg 3] ;; .ret (.reg 4))

/-- Writing the answer allocates exactly one scalar block. A reversed
source must fit after exact negation. -/
noncomputable def queryOutputContract (w h P : ℕ) : Contract :=
  let C := heapContract w
    (fun args mem => ∃ src direction L heap, args = [src, direction, L, heap] ∧
      direction ≤ 1 ∧ src + L ≤ heap ∧ Num.Valid mem src h L ∧
      (direction = 0 → Num.Fits h L (-Num.intVal mem src h L)))
    (fun args mem mem' =>
      ScalarAt mem' (heapArg args) h (args.getD 2 0) P
        (if args.getD 1 0 = 0 then
          -Num.fixVal mem (args.getD 0 0) h (args.getD 2 0) P
        else Num.fixVal mem (args.getD 0 0) h (args.getD 2 0) P))
    (fun args _ => 36 * args.getD 2 0 + 24) (fun args _ => args.getD 2 0)
  { C with post := fun args mem v mem' =>
    v = heapArg args + args.getD 2 0 ∧ C.post args mem v mem' }

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM IPM.Machine

/-- Both branches use deterministic instructions. -/
theorem queryOutputBody_noRand (copy negate : ℕ) : (queryOutputBody copy negate).NoRand := by
  simp [queryOutputBody, Stmt.NoRand]

private theorem outputScalar {mem mem' : ℕ → ℕ} {src heap h L P : ℕ}
    {reverse : Bool} (hv : Num.Valid mem' heap h L)
    (he : Num.intVal mem' heap h L =
      if reverse then -Num.intVal mem src h L else Num.intVal mem src h L) :
    ScalarAt mem' heap h L P
      (if reverse then -Num.fixVal mem src h L P else Num.fixVal mem src h L P) := by
  refine ⟨hv, ?_⟩
  cases reverse <;> simp [Num.fixVal, he, Int.cast_neg, neg_div]

/-- The Query output body meets its contract for every random tape,
using the verified copy and negate procedures. -/
theorem queryOutput_meetsContract {w h P base copy negate : ℕ} {p : Program}
    (hp : p.HasAt base [queryOutputBody copy negate])
    (hc : MeetsContract w p copy (Num.copyContract w h))
    (hn : MeetsContract w p negate (Num.negateContract w h)) :
    MeetsContract w p base (queryOutputContract w h P) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨src, direction, L, heap, rfl, hdir, hsrc, hv, hneg⟩, hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + L < 2 ^ w at hroom
  have hw : ∀ x ∈ [src, L, heap], x < 2 ^ w := by
    intro x hx
    apply hwords
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (show x = src ∨ x = direction ∨ x = L ∨ x = heap from by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with he | he | he
        · exact Or.inl he
        · exact Or.inr (Or.inr (Or.inl he))
        · exact Or.inr (Or.inr (Or.inr he)))
  let st := startState [src, direction, L, heap] mem pos
  let Q : Outcome → State → Prop := fun o s =>
    (queryOutputContract w h P).post [src, direction, L, heap] mem o.value s.mem
  have ht : Triple w p (fun s => s = st ∧ direction ≠ 0)
      (.call 4 copy [.reg 0, .reg 2, .reg 3] ;; .ret (.reg 4)) Q
      (fun _ => 36 * L + 22) := by
    intro s tape ⟨hs, hd⟩
    subst s
    apply runs_start_le
    refine runs_seq_call_le hc (vs := [src, L, heap]) (by rfl) hw
      ⟨⟨src, L, heap, rfl, hsrc, hv⟩, hz, hroom⟩ ?_
    intro v mem' pos' hout
    rcases hout with ⟨he, hlo, hhi, hframe, hz', _, hv', he'⟩
    refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
    · refine ⟨he, hlo, hhi, hframe, hz', ?_⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero, hd, ↓reduceIte]
      exact outputScalar (reverse := false) hv' he'
    · change 0 + 3 + (17 * L + 12) + 2 + 2 ≤ 36 * L + 22
      omega
  have hf : Triple w p (fun s => s = st ∧ direction = 0)
      (.call 4 negate [.reg 0, .reg 2, .reg 3] ;; .ret (.reg 4)) Q
      (fun _ => 36 * L + 22) := by
    intro s tape ⟨hs, hd⟩
    subst s
    apply runs_start_le
    refine runs_seq_call_le hn (vs := [src, L, heap]) (by rfl) hw
      ⟨src, L, heap, rfl, ⟨⟨src, L, 1, heap, rfl, hsrc, le_rfl, hv⟩, hz, hroom⟩⟩ ?_
    intro v mem' pos' hout
    rcases hout with ⟨he, hlo, hhi, hframe, hz', hdigits⟩
    obtain ⟨hv', he'⟩ := Num.negateCarry_value_one hv hdigits
    rw [Num.wrap_of_fits (hneg hd)] at he'
    refine runs_ret_le (v := v) (by eval_expr) ?_ ?_
    · refine ⟨he, hlo, hhi, hframe, hz', ?_⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero, hd, ↓reduceIte]
      exact outputScalar (reverse := true) hv' he'
    · change 0 + 3 + (36 * L + 14) + 2 + 2 ≤ 36 * L + 22
      omega
  have hall := Triple.cond_const (w := w) (p := p) (e := .reg 1)
    (val := fun _ => direction) (P := fun s => s = st)
    (fun _ hs => hs ▸ rfl) ht hf
  obtain ⟨o, st', c, hr, hpost, hcost⟩ := hall st ω rfl
  refine ⟨o, st', c, hr, hpost, ?_⟩
  simp only [Expr.size_reg, max_self] at hcost
  change c ≤ 36 * L + 24
  omega

end MinCostFlow.MinRatio
