module

public import MinCostFlow.LSF.Program.THResult
public import MinCostFlow.LSF.Program.THSize
public import MinCostFlow.LSF.Program.THHeavy
public import MinCostFlow.LSF.Program.THPlace

/-!
# The auxiliary tree `T_H` in one procedure

`thProc` runs the five passes of `T_H` one after the other on a scratch area of `8 n` zero words
at `base`. Array `c` of the area starts at `base + c n`: `0` the sums `acc`, `1` the subtree
sizes, `2` the tops, `3` the chain sizes, `4` the block starts, `5` the chain array, `6` the
parents in `T_H` and `7` the depths in `T_H`. The inputs are the top-down order `Q` and the
parent and depth arrays of the rooted tree `T₀` (`TreeIdx`).

`thProc_meetsContract` shows that array `6` holds the parent in `T_H = hldAuxTree T₀ r₀` of every
vertex other than the root, and array `7` the depth in `T_H` of every vertex. The cost is
`O(n log n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- The address `base + c n` of array `c` (registers `4 = base`, `0 = n`). -/
def thAddr (c : ℕ) : Expr := .bin .add (.reg 4) (.bin .mul (.const c) (.reg 0))

/-- Args: `[n, qPtr, parPtr, depPtr, base]`. -/
def thProc (bSize bHeavy bOff bPlace bDepth : ℕ) : Stmt :=
  .call 19 bSize [.reg 0, .reg 1, .reg 2, .reg 4, thAddr 1] ;;
  .call 19 bHeavy [.reg 0, .reg 1, .reg 2, thAddr 1, thAddr 2, thAddr 3] ;;
  .call 19 bOff [.reg 0, thAddr 2, thAddr 3, thAddr 4] ;;
  .call 19 bPlace [.reg 0, thAddr 2, .reg 3, thAddr 4, thAddr 5] ;;
  .call 19 bDepth [.reg 0, .reg 1, .reg 2, thAddr 2, .reg 3, thAddr 3, thAddr 4, thAddr 5,
    thAddr 6, thAddr 7] ;;
  .ret (.const 0)

lemma thProc_noRand (bSize bHeavy bOff bPlace bDepth : ℕ) :
    (thProc bSize bHeavy bOff bPlace bDepth).NoRand := by
  simp [thProc, Stmt.NoRand]

/-- The output of `thProc`: parents and depths in `T_H`, for every tree that the input arrays
describe. -/
def THOut (mem mem' : ℕ → ℕ) (n qPtr parPtr depPtr base : ℕ) : Prop :=
  ∀ (Q : List ℕ) (r tM : ℕ) (T₀ : MGraph) (vList : List ℕ) (fid tl hd pe : ℕ → ℕ),
    vList.length = n → TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
    TreeIdx T₀ vList tM r fid tl hd (fun x => mem (parPtr + x)) pe (fun x => mem (depPtr + x)) →
    (∀ x < n, mem (depPtr + x) < n) →
    ∀ x < n,
      mem' (base + 7 * n + x) =
        depth (hldAuxTree T₀ (vList.getD r 0)) (vList.getD r 0) (vList.getD x 0) ∧
      (x ≠ r → mem' (base + 6 * n + x) < n ∧ vList.getD (mem' (base + 6 * n + x)) 0 =
        thParent T₀ (vList.getD r 0) (vList.getD x 0))

/-- The first part of the search result satisfies any property of `above` and of the
segment. -/
lemma bstIdx_fst_prop (P : ℕ → Prop) {A : ℕ → ℕ} :
    ∀ len above lo j, P above → (∀ k < len, P (A (lo + k))) → P (bstIdx above A lo len j).1 := by
  intro len
  induction len using Nat.strong_induction_on with
  | h len ih =>
    intro above lo j ha hA
    rw [bstIdx.eq_def]
    by_cases h0 : len = 0
    · simp [h0, ha]
    · have hm : len / 2 < len := Nat.div_lt_self (by omega) (by decide)
      simp only [h0, dite_false]
      split_ifs with h1 h2
      · exact ha
      · exact ih _ hm _ _ _ (hA _ hm) (fun k hk => hA k (by omega))
      · refine ih _ (by omega) _ _ _ (hA _ hm) (fun k hk => ?_)
        have := hA (len / 2 + 1 + k) (by omega)
        rwa [show lo + (len / 2 + 1 + k) = lo + len / 2 + 1 + k by omega] at this

/-- The parent in `T_H` is an index. -/
lemma thPar_lt_of {n r : ℕ} {Q : List ℕ} {par top dep cnt off arr thPar : ℕ → ℕ} {B : ℕ}
    {D : ℕ → ℕ} (hIn : THDepthIn n r Q par top dep cnt off arr B D) {x : ℕ} (hx : x < n)
    (hpx : par x < n) (hP : ParRule par top dep cnt off arr thPar x) : thPar x < n := by
  rw [hP]
  split_ifs
  · exact hpx
  · unfold thR
    refine bstIdx_fst_prop (· < n) _ _ _ _ (hIn.top_lt x hx) (fun k hk => hIn.arr_lt _ ?_)
    have := hIn.blk x hx
    omega

/-- The contract of `thProc`. The inputs lie below `base`, and the scratch area is zero. -/
def thContract (w : ℕ) : Contract where
  pre args mem := ∃ (n qPtr parPtr depPtr base r tM : ℕ) (Q : List ℕ) (T₀ : MGraph)
      (vList : List ℕ) (fid tl hd pe : ℕ → ℕ),
    args = [n, qPtr, parPtr, depPtr, base] ∧ 0 < n ∧ vList.length = n ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    TreeIdx T₀ vList tM r fid tl hd (fun x => mem (parPtr + x)) pe (fun x => mem (depPtr + x)) ∧
    (∀ x < n, mem (depPtr + x) < n) ∧
    qPtr + n ≤ base ∧ parPtr + n ≤ base ∧ depPtr + n ≤ base ∧ base + 8 * n < 2 ^ w ∧
    thBound n + 2 * n + 8 < 2 ^ w ∧ (∀ a, base ≤ a → a < base + 8 * n → mem a = 0)
  post args mem ret mem' := ∃ (n qPtr parPtr depPtr base : ℕ),
    args = [n, qPtr, parPtr, depPtr, base] ∧ ret = 0 ∧
    (∀ a, a < base ∨ base + 8 * n ≤ a → mem' a = mem a) ∧
    THOut mem mem' n qPtr parPtr depPtr base
  cost args _ := args.getD 0 0 * (bstLoopCost (args.getD 0 0) + 500) + 500

theorem thProc_meetsContract {w : ℕ} {p : Program} {b bSize bHeavy bOff bPlace bDepth : ℕ}
    (hp : p.procs[b]? = some (thProc bSize bHeavy bOff bPlace bDepth))
    (hSize : MeetsContract w p bSize (thSizeContract w))
    (hHeavy : MeetsContract w p bHeavy (thHeavyContract w))
    (hOff : MeetsContract w p bOff (thOffContract w))
    (hPlace : MeetsContract w p bPlace (thPlaceContract w))
    (hDepth : MeetsContract w p bDepth (thDepthContract w)) :
    MeetsContract w p b (thContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, qPtr, parPtr, depPtr, base, r, tM, Q, T₀, vList, fid, tl, hd, pe, rfl, hn, hvn, hQ,
    hQat, hI, hdep, hqb, hpb, hdb, hbw, hBw, hz⟩ := hpre
  set args := [n, qPtr, parPtr, depPtr, base] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hR0 : ∀ i < 5, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 5, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hrn : r < n := by
    have h0 := hQ.head_eq hn
    rw [← h0]; exact hQ.lt _ (List.getElem_mem _)
  have hcw : ∀ c ≤ 8, base + c * n < 2 ^ w := fun c hc => by
    have : c * n ≤ 8 * n := Nat.mul_le_mul_right n hc
    omega
  have hQlen := hQ.len
  set par : ℕ → ℕ := fun x => mem (parPtr + x) with hpar
  set dep : ℕ → ℕ := fun x => mem (depPtr + x) with hdepf
  -- the inputs below `base` stay
  have hlow : ∀ memX : ℕ → ℕ, (∀ a < base, memX a = mem a) →
      (∀ x < n, memX (parPtr + x) = par x) ∧ (∀ x < n, memX (depPtr + x) = dep x) ∧
      TopDownOrder n r (fun x => memX (parPtr + x)) Q ∧ ListAt memX qPtr Q := by
    intro memX hX
    have hpX : ∀ x < n, memX (parPtr + x) = par x := fun x hx => hX _ (by omega)
    exact ⟨hpX, fun x hx => hX _ (by omega), hQ.congr (fun x hx => (hpX x hx).symm),
      fun i hi => by rw [hX _ (by rw [hQlen] at hi; omega)]; exact hQat i hi⟩
  refine runs_start_le ?_
  unfold thProc
  simp only [thAddr]
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have hc1 := hcw 1 (by omega)
  have hc2 := hcw 2 (by omega)
  have hc3 := hcw 3 (by omega)
  have hc4 := hcw 4 (by omega)
  have hc5 := hcw 5 (by omega)
  have hc6 := hcw 6 (by omega)
  have hc7 := hcw 7 (by omega)
  -- 1. sizes
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, base, base + 1 * n]) hSize
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 4 (by omega)
      · exact hc1)
    ⟨n, qPtr, parPtr, base, base + 1 * n, r, Q, rfl, hn, hQ, hQat, by omega, by omega, by omega,
      by omega, fun u hu => hz _ (by omega) (by omega)⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨n', qPtr', parPtr', accPtr', szPtr', heq₁, -, hfr₁, hS₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hS₁
  obtain ⟨hS, hSr⟩ := hS₁ Q r hQ hQat
  obtain ⟨hp₁, hd₁, hQ₁, hQat₁⟩ := hlow mem₁ (fun a ha => hfr₁ a (Or.inl ha))
  set sz : ℕ → ℕ := fun x => mem₁ (base + 1 * n + x) with hszf
  have hszle : ∀ x < n, sz x ≤ n := by
    have hQv : TopDownOrder vList.length r par Q := by rw [hvn]; exact hQ
    have hSv : SizeState Q par vList.length (fun u => mem₁ (base + u)) sz 1 := by
      rw [hvn]; exact hS
    have := sz_le_of hI hQv hSv hSr
    rw [hvn] at this; exact this
  -- 2. heavy children and tops
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, base + 1 * n, base + 2 * n, base + 3 * n])
    hHeavy
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _)))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hc1
      · exact hc2
      · exact hc3)
    ⟨n, qPtr, parPtr, base + 1 * n, base + 2 * n, base + 3 * n, r, Q, rfl, hn, hQ₁, hQat₁,
      by omega, by omega, by omega, by omega, by omega, hszle,
      fun t ht => by
        show mem₁ _ = 0
        rw [hfr₁ _ (Or.inr (by omega))]; exact hz _ (by omega) (by omega)⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨n', qPtr', parPtr', szPtr', topPtr', cntPtr', heq₂, -, hfr₂, hH₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hH₂
  have hH₁ := hH₂ Q r hQ₁ hQat₁
  have hH := heavyState_congr_input hQ₁ (par' := par) (sz' := sz) (fun x hx => (hp₁ x hx).symm)
    (fun x _ => rfl) hH₁
  obtain ⟨hp₂, hd₂, hQ₂, hQat₂⟩ := hlow mem₂ (fun a ha => (hfr₂ a (Or.inl (by omega))).trans
    (hfr₁ a (Or.inl ha)))
  set top : ℕ → ℕ := fun x => mem₂ (base + 2 * n + x) with htopf
  set cnt : ℕ → ℕ := fun x => mem₂ (base + 3 * n + x) with hcntf
  have htn : ∀ x < n, top x < n := fun x hx => hH.2.1 x (by
    rw [List.take_of_length_le (by rw [hQ.len])]; exact hQ.cover x hx)
  -- the tree facts so far, for the bounds
  have hQv : TopDownOrder vList.length r par Q := by rw [hvn]; exact hQ
  have hSv : SizeState Q par vList.length (fun u => mem₁ (base + u)) sz 1 := by
    rw [hvn]; exact hS
  have hHv : HeavyState Q par vList.length r sz top cnt vList.length := by rw [hvn]; exact hH
  have hsz := size_bridge hI.hT hI.hA hI.hnd hI.hV hI.hR hI.hr hQv hSv hSr
  have hB : TopsSpec T₀ vList r top :=
    heavy_bridge hI.hT hI.hA hI.hnd hI.hV hI.hR hI.hr hQv hsz hHv
  have hC := fun t ht htt => heavy_count hI.hT hI.hnd hI.hV hQv hHv hB (t := t) ht htt
  have hcard := cnt_card_of_heavyState hQv hHv
  have htt : ∀ x < vList.length, top (top x) = top x := fun x hx => top_top hI hB hx
  -- 3. block starts
  refine runs_seq_call_le (vs := [n, base + 2 * n, base + 3 * n, base + 4 * n]) hOff
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hc2
      · exact hc3
      · exact hc4)
    ⟨n, base + 2 * n, base + 3 * n, base + 4 * n, rfl, hn, by omega, by omega, by omega,
      fun t ht => by
        have := offSum_le hcard htt (t := t) (by omega)
        rw [hvn] at this; exact this⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n', topPtr', cntPtr', offPtr', heq₃, -, hfr₃, hO₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hO₃
  obtain ⟨hp₃, hd₃, hQ₃, hQat₃⟩ := hlow mem₃ (fun a ha => (hfr₃ a (Or.inl (by omega))).trans
    ((hfr₂ a (Or.inl (by omega))).trans (hfr₁ a (Or.inl ha))))
  set off : ℕ → ℕ := fun x => mem₃ (base + 4 * n + x) with hofff
  have ht₃ : ∀ x < n, mem₃ (base + 2 * n + x) = top x := fun x hx => hfr₃ _ (Or.inl (by omega))
  have hc₃ : ∀ x < n, mem₃ (base + 3 * n + x) = cnt x := fun x hx => hfr₃ _ (Or.inl (by omega))
  have hslot₃ : ∀ x < n, thSlot (fun t => mem₃ (base + 4 * n + t)) (fun t => mem₃ (base + 2 * n + t))
      (fun t => mem₃ (depPtr + t)) x = thSlot (offSum top cnt) top dep x := by
    intro x hx
    unfold thSlot
    dsimp only
    rw [ht₃ x hx, hd₃ x hx, hd₃ _ (htn x hx)]
    rw [show mem₃ (base + 4 * n + top x) = offSum top cnt (top x) from hO₃ _ (htn x hx)]
  -- 4. the chain array
  refine runs_seq_call_le (vs := [n, base + 2 * n, depPtr, base + 4 * n, base + 5 * n]) hPlace
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hc2
      · exact hwa 3 (by omega)
      · exact hc4
      · exact hc5)
    ⟨n, base + 2 * n, depPtr, base + 4 * n, base + 5 * n, rfl, hn, by omega, by omega, by omega,
      by omega, fun x hx => by dsimp only; rw [ht₃ x hx]; exact htn x hx,
      fun x hx => by dsimp only; rw [hd₃ x hx]; exact hdep x hx,
      fun x hx => by
        dsimp only
        rw [hslot₃ x hx]
        have := thSlot_lt hI hB hC hcard (x := x) (by omega)
        rw [hvn] at this; exact this,
      fun x hx y hy hxy => by
        dsimp only at hxy
        rw [hslot₃ x hx, hslot₃ y hy] at hxy
        exact thSlot_inj hI hB hC (by omega) (by omega) hxy⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨n', topPtr', depPtr', offPtr', arrPtr', heq₄, -, hfr₄, hP₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hP₄
  obtain ⟨hp₄, hd₄, hQ₄, hQat₄⟩ := hlow mem₄ (fun a ha => (hfr₄ a (Or.inl (by omega))).trans
    ((hfr₃ a (Or.inl (by omega))).trans ((hfr₂ a (Or.inl (by omega))).trans
      (hfr₁ a (Or.inl ha)))))
  set arr : ℕ → ℕ := fun x => mem₄ (base + 5 * n + x) with harrf
  have harr : ∀ x < n, arr (thSlot (offSum top cnt) top dep x) = x := by
    intro x hx
    rw [← hslot₃ x hx]; exact hP₄ x hx
  have ht₄ : ∀ x < n, mem₄ (base + 2 * n + x) = top x := fun x hx =>
    (hfr₄ _ (Or.inl (by omega))).trans (ht₃ x hx)
  have hc₄ : ∀ x < n, mem₄ (base + 3 * n + x) = cnt x := fun x hx =>
    (hfr₄ _ (Or.inl (by omega))).trans (hc₃ x hx)
  have ho₄ : ∀ x < n, mem₄ (base + 4 * n + x) = off x := fun x hx => hfr₄ _ (Or.inl (by omega))
  -- `THArrays` for any tree that the inputs describe, in the arrays the last pass reads
  have hArr : ∀ (T₀' : MGraph) (vList' : List ℕ) (tM' : ℕ) (fid' tl' hd' pe' : ℕ → ℕ),
      vList'.length = n → TreeIdx T₀' vList' tM' r fid' tl' hd' par pe' dep →
      (∀ x < n, dep x < n) →
      THArrays T₀' vList' tM' r fid' tl' hd' (fun x => mem₄ (parPtr + x)) pe'
        (fun x => mem₄ (depPtr + x)) Q sz (fun x => mem₄ (base + 2 * n + x))
        (fun x => mem₄ (base + 3 * n + x)) (fun x => mem₄ (base + 4 * n + x)) arr := by
    intro T₀' vList' tM' fid' tl' hd' pe' hvn' hI' hdep'
    subst hvn'
    have h0 := thArrays_of hI' hQ hS hSr hH (off := off) (arr := arr)
      (fun t ht => hO₃ t ht) harr hdep'
    exact h0.congr hp₄ hd₄ (fun _ _ => rfl) ht₄ hc₄ ho₄ (fun _ _ => rfl)
  have hA := hArr T₀ vList tM fid tl hd pe hvn hI hdep
  have hDin := thDepthIn_of hA
  rw [hvn] at hDin
  -- 5. parents and depths in `T_H`
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, base + 2 * n, depPtr, base + 3 * n,
      base + 4 * n, base + 5 * n, base + 6 * n, base + 7 * n]) hDepth
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hc2
      · exact hwa 3 (by omega)
      · exact hc3
      · exact hc4
      · exact hc5
      · exact hc6
      · exact hc7)
    ⟨n, qPtr, parPtr, base + 2 * n, depPtr, base + 3 * n, base + 4 * n, base + 5 * n,
      base + 6 * n, base + 7 * n, r, thBound n, Q, _, rfl, hn, hQ₄, hQat₄, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, hBw,
      fun y hy => by
        dsimp only
        rw [hfr₄ _ (Or.inr (by omega)), hfr₃ _ (Or.inr (by omega)), hfr₂ _ (Or.inr (by omega)),
          hfr₁ _ (Or.inr (by omega))]
        have := hz (base + 7 * n + y) (by omega) (by omega)
        simp only [startState]; omega, hDin⟩ ?_
  rintro v₅ mem₅ pos₅ ⟨n', qPtr', parPtr', topPtr', depPtr', cntPtr', offPtr', arrPtr',
    thParPtr', dthPtr', heq₅, -, hfr₅, hD₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr₅ hD₅
  obtain ⟨hpr, hdr, hrules⟩ := hD₅ Q r hQ₄ hQat₄
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, qPtr, parPtr, depPtr, base, rfl, rfl,
    fun a ha => ?_, ?_⟩ ?_
  · show mem₅ a = mem a
    rcases ha with ha | ha
    · rw [hfr₅ a (Or.inl (by omega)), hfr₄ a (Or.inl (by omega)), hfr₃ a (Or.inl (by omega)),
        hfr₂ a (Or.inl (by omega)), hfr₁ a (Or.inl ha)]
      rfl
    · rw [hfr₅ a (Or.inr (by omega)), hfr₄ a (Or.inr (by omega)), hfr₃ a (Or.inr (by omega)),
        hfr₂ a (Or.inr (by omega)), hfr₁ a (Or.inr (by omega))]
      rfl
  · intro Q' r' tM' T₀' vList' fid' tl' hd' pe' hvn' hQ' hQat' hI' hdep'
    have hQQ := topDownOrder_eq_of_listAt hQ hQ' hQat hQat'
    subst hQQ
    have hr' : r' = r := by rw [← hQ'.head_eq hn, hQ.head_eq hn]
    subst hr'
    have hA' := hArr T₀' vList' tM' fid' tl' hd' pe' hvn' hI' hdep'
    have hbr := th_bridge hA' (thPar := fun x => mem₅ (base + 6 * n + x))
      (dTH := fun x => mem₅ (base + 7 * n + x)) hdr (by rw [hvn']; exact hrules)
    rw [hvn'] at hbr
    have hDin' := thDepthIn_of hA'
    rw [hvn'] at hDin'
    intro x hx
    refine ⟨(hbr x hx).1, fun hxr => ⟨thPar_lt_of (thPar := fun x => mem₅ (base + 6 * n + x))
      hDin' hx ?_ (hrules x hx hxr).1, (hbr x hx).2 hxr⟩⟩
    have := hI'.hR.par_lt x (by rw [hvn']; exact hx)
    rw [hvn'] at this
    show mem₄ (parPtr + x) < n
    rw [hp₄ x hx]; exact this
  · simp [thContract, thSizeContract, thHeavyContract, thOffContract, thPlaceContract,
      thDepthContract, hargs, argsSize, Expr.size]
    have : n * (bstLoopCost n + 500) = n * (bstLoopCost n + 200) + 300 * n := by ring
    omega

end

end MinCostFlow.LSF.Program
