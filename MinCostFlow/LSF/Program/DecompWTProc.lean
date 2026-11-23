module

public import MinCostFlow.LSF.Program.DecompDeg
public import MinCostFlow.LSF.Program.DecompGreedy
public import MinCostFlow.LSF.Program.DecompLabel
public import MinCostFlow.LSF.Program.DecompMark
public import MinCostFlow.LSF.Program.DecompClosure

/-!
# The five passes of `W_T` in one procedure

`decompWTProc` runs the degree, greedy, label, mark and closure passes one after the other on a
scratch area of `12 n` zero words at `base`. Array `c` of the area starts at `base + c n`:
`0` degrees, `1` weights `ν`, `2` open sums, `3` batch counts `nb`, `4` batch numbers `bidx`,
`5` bag weights, `6`, `7` labels, `8` marks, `9` child counts, `10` `has`, `11` the boundary
flags. `DecompWTOut` lists what the passes give, which is what `wT_spec` (`DecompWT.lean`) needs.
The cost is `O(m0 + n)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow

@[expose] public section

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

lemma procChildren_congr_par (hQ : TopDownOrder n r par Q) {par' : ℕ → ℕ}
    (hpar : ∀ x < n, par x = par' x) (u j : ℕ) :
    procChildren Q par u j = procChildren Q par' u j := by
  unfold procChildren
  refine List.filter_congr (fun c hc => ?_)
  rw [hpar c (hQ.lt c (List.mem_of_mem_drop (List.mem_reverse.mp hc)))]

/-- The greedy invariant only reads the parents and weights below `n`. -/
lemma greedyState_congr_input (hQ : TopDownOrder n r par Q) {par' : ℕ → ℕ} {θ : ℕ}
    {ν ν' cur nb bidx s : ℕ → ℕ} {j : ℕ} (hpar : ∀ x < n, par x = par' x)
    (hν : ∀ x < n, ν x = ν' x) (hG : GreedyState Q par n θ ν cur nb bidx s j) :
    GreedyState Q par' n θ ν' cur nb bidx s j := by
  obtain ⟨h1, h2, h3⟩ := hG
  refine ⟨fun u hu => ?_, fun x hx => ?_, h3⟩
  · rw [← procChildren_congr_par hQ hpar u j]; exact h1 u hu
  · rw [← hν x (hQ.lt x (List.mem_of_mem_drop hx))]; exact h2 x hx

/-- The closure invariant only reads the parents and marks below `n`. -/
lemma closureState_congr_input (hQ : TopDownOrder n r par Q) {par' : ℕ → ℕ}
    {S S' cnt has inR : ℕ → ℕ} {j : ℕ} (hpar : ∀ x < n, par x = par' x)
    (hS : ∀ x < n, S x = S' x) (hC : ClosureState Q par n S cnt has inR j) :
    ClosureState Q par' n S' cnt has inR j := by
  obtain ⟨h1, h2⟩ := hC
  refine ⟨fun u hu => ?_, fun x hx => ?_⟩
  · rw [h1 u hu]
    congr 1
    refine List.filter_congr (fun c hc => ?_)
    rw [hpar c (hQ.lt c (List.mem_of_mem_drop hc))]
  · rw [← hS x (hQ.lt x (List.mem_of_mem_drop hx))]; exact h2 x hx

/-- After the greedy pass, every batch number off the root is below `n`. -/
lemma greedyState_bidx_lt (hQ : TopDownOrder n r par Q) (hn : 0 < n) {θ : ℕ}
    {ν cur nb bidx s : ℕ → ℕ} (hG : GreedyState Q par n θ ν cur nb bidx s 1) :
    ∀ x < n, x ≠ r → bidx x < n := by
  intro x hx hxr
  obtain ⟨i, hi, hQi⟩ := List.getElem_of_mem (hQ.cover x hx)
  have hp := hQ.after i hi (by rw [hQi]; exact hxr)
  rw [hQi] at hp
  have hpn : par x < n := hQ.lt _ (List.mem_of_mem_take hp)
  have hmem : x ∈ procChildren Q par (par x) 1 := by
    unfold procChildren
    rw [List.mem_filter, List.mem_reverse, decide_eq_true_iff]
    exact ⟨(hQ.mem_drop_one hn).mpr ⟨hx, hxr⟩, rfl⟩
  have hrun := hG.1 (par x) hpn
  have hb := ((DecompGen.onlineRun_bounds _ _ _ _ _ _ _ _ hrun).2 x hmem).2
  have hnb := onlineRun_nb_le _ _ _ _ _ hrun
  have hlen := procChildren_length_lt hQ (par x) 1 le_rfl hn
  omega

lemma labelRule_congr {par nb bidx labY labB par' nb' bidx' labY' labB' : ℕ → ℕ} {r x : ℕ}
    (hx : x < n) (hpx : par x < n)
    (h : ∀ y < n, par y = par' y ∧ nb y = nb' y ∧ bidx y = bidx' y ∧ labY y = labY' y ∧
      labB y = labB' y)
    (hL : LabelRule par nb bidx labY labB r x) : LabelRule par' nb' bidx' labY' labB' r x := by
  unfold LabelRule at hL ⊢
  obtain ⟨h1, -, h3, h4, h5⟩ := h x hx
  rw [← h1, ← h3, ← h4, ← h5]
  obtain ⟨-, h2', -, h4', h5'⟩ := h (par x) hpx
  rw [← h2', ← h4', ← h5']
  exact hL

lemma rootFlag_congr {par bidx nb par' bidx' nb' : ℕ → ℕ} {r : ℕ} (hr : r < n)
    (h : ∀ y < n, par y = par' y ∧ bidx y = bidx' y ∧ nb y = nb' y) :
    rootFlag par bidx nb r n = rootFlag par' bidx' nb' r n := by
  classical
  unfold rootFlag
  have hiff : (∃ x < n, x ≠ r ∧ par x = r ∧ bidx x = nb r) ↔
      (∃ x < n, x ≠ r ∧ par' x = r ∧ bidx' x = nb' r) := by
    constructor
    · rintro ⟨x, hx, h1, h2, h3⟩
      exact ⟨x, hx, h1, (h x hx).1 ▸ h2, by rw [← (h x hx).2.1, ← (h r hr).2.2]; exact h3⟩
    · rintro ⟨x, hx, h1, h2, h3⟩
      exact ⟨x, hx, h1, (h x hx).1 ▸ h2, by rw [(h x hx).2.1, (h r hr).2.2]; exact h3⟩
  by_cases hc : ∃ x < n, x ≠ r ∧ par x = r ∧ bidx x = nb r
  · rw [ite_eq_left hc, ite_eq_left (hiff.mp hc)]
  · rw [ite_eq_right hc, ite_eq_right (fun h' => hc (hiff.mpr h'))]

/-- What the five passes leave in the scratch area at `base` (`mem'`), for the inputs in `mem`. -/
def DecompWTOut (mem mem' : ℕ → ℕ) (n m0 euPtr evPtr qPtr parPtr r θ base : ℕ) : Prop :=
  (∀ x < n, mem' (base + x) =
      degCount (fun t => mem (euPtr + t)) (fun t => mem (evPtr + t)) m0 x ∧
    mem' (base + 1 * n + x) =
      degNu θ (degCount (fun t => mem (euPtr + t)) (fun t => mem (evPtr + t)) m0 x)) ∧
  (∀ Q, TopDownOrder n r (fun x => mem (parPtr + x)) Q → ListAt mem qPtr Q →
    GreedyState Q (fun x => mem (parPtr + x)) n θ (fun x => mem' (base + 1 * n + x))
      (fun x => mem' (base + 2 * n + x)) (fun x => mem' (base + 3 * n + x))
      (fun x => mem' (base + 4 * n + x)) (fun x => mem' (base + 5 * n + x)) 1 ∧
    ClosureState Q (fun x => mem (parPtr + x)) n (fun x => mem' (base + 8 * n + x))
      (fun x => mem' (base + 9 * n + x)) (fun x => mem' (base + 10 * n + x))
      (fun x => mem' (base + 11 * n + x)) 1) ∧
  (∀ x < n, x ≠ r → LabelRule (fun x => mem (parPtr + x)) (fun x => mem' (base + 3 * n + x))
    (fun x => mem' (base + 4 * n + x)) (fun x => mem' (base + 6 * n + x))
    (fun x => mem' (base + 7 * n + x)) r x) ∧
  (∀ x < n, x ≠ r → mem' (base + 8 * n + x) =
    markVal θ (mem' (base + 3 * n + x)) (mem' (base + x))) ∧
  mem' (base + 8 * n + r) = rootMarkVal θ (mem' (base + 3 * n + r)) (mem' (base + r))
    (rootFlag (fun x => mem (parPtr + x)) (fun x => mem' (base + 4 * n + x))
      (fun x => mem' (base + 3 * n + x)) r n) ∧
  mem' (base + 11 * n + r) = closureIn (mem' (base + 8 * n + r)) (mem' (base + 9 * n + r)) ∧
  (∀ x < n, mem' (base + 6 * n + x) < n ∧ mem' (base + 7 * n + x) < n)

/-- The address `base + c n` of array `c` (registers `8 = base`, `0 = n`). -/
def wtAddr (c : ℕ) : Expr := .bin .add (.reg 8) (.bin .mul (.const c) (.reg 0))

/-- Args: `[n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base]`. -/
def decompWTProc (bDeg bGreedy bLabel bMark bClosure : ℕ) : Stmt :=
  .call 19 bDeg [.reg 1, .reg 2, .reg 3, .reg 0, .reg 7, .reg 8, wtAddr 1] ;;
  .call 19 bGreedy [.reg 0, .reg 4, .reg 5, wtAddr 1, .reg 7, wtAddr 2, wtAddr 3, wtAddr 4,
    wtAddr 5] ;;
  .call 19 bLabel [.reg 0, .reg 4, .reg 5, .reg 6, wtAddr 3, wtAddr 4, wtAddr 6, wtAddr 7] ;;
  .call 19 bMark [.reg 0, .reg 5, .reg 6, wtAddr 3, wtAddr 4, .reg 8, .reg 7, wtAddr 8] ;;
  .call 19 bClosure [.reg 0, .reg 4, .reg 5, wtAddr 8, wtAddr 9, wtAddr 10, wtAddr 11] ;;
  .ret (.const 0)

lemma decompWTProc_noRand (bDeg bGreedy bLabel bMark bClosure : ℕ) :
    (decompWTProc bDeg bGreedy bLabel bMark bClosure).NoRand := by
  simp [decompWTProc, Stmt.NoRand]

/-- The contract of `decompWTProc`. The inputs lie below `base`, and the scratch area is zero. -/
def decompWTContract (w : ℕ) : Contract where
  pre args mem := ∃ (n m0 euPtr evPtr qPtr parPtr r θ base : ℕ) (Q : List ℕ),
    args = [n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base] ∧ 16 ≤ 2 ^ w ∧ 0 < n ∧ 0 < θ ∧
    3 * θ < 2 ^ w ∧ 2 * m0 < 2 ^ w ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qPtr Q ∧
    euPtr + m0 ≤ base ∧ evPtr + m0 ≤ base ∧ qPtr + n ≤ base ∧ parPtr + n ≤ base ∧
    base + 12 * n < 2 ^ w ∧
    (∀ t < m0, mem (euPtr + t) < n ∧ mem (evPtr + t) < n) ∧
    (∀ a, base ≤ a → a < base + 12 * n → mem a = 0)
  post args mem ret mem' := ∃ (n m0 euPtr evPtr qPtr parPtr r θ base : ℕ),
    args = [n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base] ∧ ret = 0 ∧
    (∀ a, a < base ∨ base + 12 * n ≤ a → mem' a = mem a) ∧
    DecompWTOut mem mem' n m0 euPtr evPtr qPtr parPtr r θ base
  cost args _ := 60 * args.getD 1 0 + 400 * args.getD 0 0 + 600

private lemma degNu_le (θ d : ℕ) : degNu θ d ≤ θ := by unfold degNu; split_ifs <;> omega

private lemma markVal_le (θ a b : ℕ) : markVal θ a b ≤ 1 := by unfold markVal; split_ifs <;> omega

private lemma rootMarkVal_le (θ a b c : ℕ) : rootMarkVal θ a b c ≤ 1 := by
  unfold rootMarkVal; split_ifs <;> omega

theorem decompWT_meetsContract {w : ℕ} {p : Program}
    {b bDeg bGreedy bLabel bMark bClosure : ℕ}
    (hp : p.procs[b]? = some (decompWTProc bDeg bGreedy bLabel bMark bClosure))
    (hDeg : MeetsContract w p bDeg (decompDegContract w))
    (hGreedy : MeetsContract w p bGreedy (decompGreedyContract w))
    (hLabel : MeetsContract w p bLabel (decompLabelContract w))
    (hMark : MeetsContract w p bMark (decompMarkContract w))
    (hClosure : MeetsContract w p bClosure (decompClosureContract w)) :
    MeetsContract w p b (decompWTContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base, Q, rfl, hw16, hn, hθ, h3θ, hm0, hQ, hQat,
    heu, hev, hqb, hpb, hbw, hends, hz⟩ := hpre
  set args := [n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base] with hargs
  have hw1 : 1 < 2 ^ w := by omega
  have hR0 : ∀ i < 9, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 9, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hrn : r < n := by
    have h0 := hQ.head_eq hn
    rw [← h0]; exact hQ.lt _ (List.getElem_mem _)
  have hcw : ∀ c ≤ 12, base + c * n < 2 ^ w := fun c hc => by
    have : c * n ≤ 12 * n := Nat.mul_le_mul_right n hc
    omega
  have hQlen := hQ.len
  -- the inputs below `base` stay; what this gives
  have hlow : ∀ memX : ℕ → ℕ, (∀ a < base, memX a = mem a) →
      (∀ x < n, memX (parPtr + x) = mem (parPtr + x)) ∧
      TopDownOrder n r (fun x => memX (parPtr + x)) Q ∧ ListAt memX qPtr Q := by
    intro memX hX
    have hpX : ∀ x < n, memX (parPtr + x) = mem (parPtr + x) := fun x hx => hX _ (by omega)
    exact ⟨hpX, hQ.congr (fun x hx => (hpX x hx).symm),
      fun i hi => by rw [hX _ (by rw [hQlen] at hi; omega)]; exact hQat i hi⟩
  refine runs_start_le ?_
  unfold decompWTProc
  simp only [wtAddr]
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  have r7 := hR0 7 (by omega)
  have r8 := hR0 8 (by omega)
  have hc1 := hcw 1 (by omega)
  have hc2 := hcw 2 (by omega)
  have hc3 := hcw 3 (by omega)
  have hc4 := hcw 4 (by omega)
  have hc5 := hcw 5 (by omega)
  have hc6 := hcw 6 (by omega)
  have hc7 := hcw 7 (by omega)
  have hc8 := hcw 8 (by omega)
  have hc9 := hcw 9 (by omega)
  have hc10 := hcw 10 (by omega)
  have hc11 := hcw 11 (by omega)
  have hmn : ∀ c, c * n = c * n := fun _ => rfl
  -- 1. degrees
  refine runs_seq_call_le (vs := [m0, euPtr, evPtr, n, θ, base, base + 1 * n]) hDeg
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 0 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega)
      · exact hc1)
    ⟨m0, euPtr, evPtr, n, θ, base, base + 1 * n, rfl, hw16, hm0, heu, hev, by omega, by omega,
      hends, fun x hx => hz _ (by omega) (by omega)⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨m0', euPtr', evPtr', n', θ', degPtr', nuPtr', heq₁, -, hfr₁, hD₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hfr₁ hD₁
  obtain ⟨hp₁, hQ₁, hQat₁⟩ := hlow mem₁ (fun a ha => hfr₁ a (Or.inl ha))
  -- 2. greedy
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, base + 1 * n, θ, base + 2 * n, base + 3 * n,
      base + 4 * n, base + 5 * n]) hGreedy
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_nil _ _))))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hc1
      · exact hwa 7 (by omega)
      · exact hc2
      · exact hc3
      · exact hc4
      · exact hc5)
    ⟨n, qPtr, parPtr, base + 1 * n, θ, base + 2 * n, base + 3 * n, base + 4 * n, base + 5 * n, r,
      Q, rfl, hn, hθ, h3θ, hQ₁, hQat₁, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, fun x hx => by dsimp only; rw [(hD₁ x hx).2]; exact degNu_le _ _,
      fun u hu => ⟨by dsimp only; rw [hfr₁ _ (Or.inr (by omega))]; exact hz _ (by omega) (by omega),
        by dsimp only; rw [hfr₁ _ (Or.inr (by omega))]; exact hz _ (by omega) (by omega)⟩⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨n', qPtr', parPtr', nuPtr', θ', curPtr', nbPtr', bidxPtr', sPtr', heq₂, -,
    hfr₂, hG₂⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₂
  try dsimp only at hfr₂ hG₂
  have hG := hG₂ Q r hQ₁ hQat₁
  obtain ⟨hp₂, hQ₂, hQat₂⟩ := hlow mem₂ (fun a ha => (hfr₂ a (Or.inl (by omega))).trans
    (hfr₁ a (Or.inl ha)))
  have hbid := greedyState_bidx_lt hQ₁ hn hG
  -- 3. labels
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, r, base + 3 * n, base + 4 * n, base + 6 * n,
      base + 7 * n]) hLabel
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hc3
      · exact hc4
      · exact hc6
      · exact hc7)
    ⟨n, qPtr, parPtr, r, base + 3 * n, base + 4 * n, base + 6 * n, base + 7 * n, Q, rfl, hn, hw16,
      hQ₂, hQat₂, by omega, by omega, by omega, by omega, by omega, by omega, hbid,
      fun x hx => ⟨by
          dsimp only; rw [hfr₂ _ (Or.inr (by omega)), hfr₁ _ (Or.inr (by omega))]
          exact hz _ (by omega) (by omega), by
          dsimp only; rw [hfr₂ _ (Or.inr (by omega)), hfr₁ _ (Or.inr (by omega))]
          exact hz _ (by omega) (by omega)⟩⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n', qPtr', parPtr', r', nbPtr', bidxPtr', labYPtr', labBPtr', heq₃, -,
    hfr₃, hL₃, hLlt⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hfr₃ hL₃ hLlt
  obtain ⟨hp₃, hQ₃, hQat₃⟩ := hlow mem₃ (fun a ha => (hfr₃ a (Or.inl (by omega))).trans
    ((hfr₂ a (Or.inl (by omega))).trans (hfr₁ a (Or.inl ha))))
  -- 4. marks
  refine runs_seq_call_le (vs := [n, parPtr, r, base + 3 * n, base + 4 * n, base, θ,
      base + 8 * n]) hMark
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hc3
      · exact hc4
      · exact hwa 8 (by omega)
      · exact hwa 7 (by omega)
      · exact hc8)
    ⟨n, parPtr, r, base + 3 * n, base + 4 * n, base, θ, base + 8 * n, rfl, hw16, hrn, by omega,
      by omega, by omega, by omega, by omega⟩ ?_
  rintro v₄ mem₄ pos₄ ⟨n', parPtr', r', nbPtr', bidxPtr', degPtr', θ', sPtr', heq₄, -, hfr₄, hS₄,
    hSr₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₄
  try dsimp only at hfr₄ hS₄ hSr₄
  obtain ⟨hp₄, hQ₄, hQat₄⟩ := hlow mem₄ (fun a ha => (hfr₄ a (Or.inl (by omega))).trans
    ((hfr₃ a (Or.inl (by omega))).trans ((hfr₂ a (Or.inl (by omega))).trans
      (hfr₁ a (Or.inl ha)))))
  -- 5. closure
  refine runs_seq_call_le (vs := [n, qPtr, parPtr, base + 8 * n, base + 9 * n, base + 10 * n,
      base + 11 * n]) hClosure
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hc8
      · exact hc9
      · exact hc10
      · exact hc11)
    ⟨n, qPtr, parPtr, base + 8 * n, base + 9 * n, base + 10 * n, base + 11 * n, r, Q, rfl, hn, hQ₄,
      hQat₄, by omega, by omega, by omega, by omega, by omega, by omega,
      fun x hx => by
        dsimp only
        by_cases hxr : x = r
        · rw [hxr, hSr₄]; exact rootMarkVal_le _ _ _ _
        · rw [hS₄ x hx hxr]; exact markVal_le _ _ _,
      fun u hu => by
        dsimp only
        rw [hfr₄ _ (Or.inr (by omega)), hfr₃ _ (Or.inr (by omega)), hfr₂ _ (Or.inr (by omega)),
          hfr₁ _ (Or.inr (by omega))]
        exact hz _ (by omega) (by omega)⟩ ?_
  rintro v₅ mem₅ pos₅ ⟨n', qPtr', parPtr', sPtr', cntPtr', hasPtr', inPtr', heq₅, -, hfr₅, hC₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₅
  try dsimp only at hfr₅ hC₅
  obtain ⟨hC, hCr⟩ := hC₅ Q r hQ₄ hQat₄
  -- what stays in the final memory
  have hA8 : ∀ a < base + 9 * n, mem₅ a = mem₄ a := fun a ha => hfr₅ a (Or.inl ha)
  have hA6 : ∀ a < base + 8 * n, mem₅ a = mem₃ a := fun a ha =>
    (hA8 a (by omega)).trans (hfr₄ a (Or.inl ha))
  have hA2 : ∀ a < base + 6 * n, mem₅ a = mem₂ a := fun a ha =>
    (hA6 a (by omega)).trans (hfr₃ a (Or.inl ha))
  have hA0 : ∀ a < base + 2 * n, mem₅ a = mem₁ a := fun a ha =>
    (hA2 a (by omega)).trans (hfr₂ a (Or.inl ha))
  have hparlt : ∀ x < n, x ≠ r → mem (parPtr + x) < n := by
    intro x hx hxr
    obtain ⟨i, hi, hQi⟩ := List.getElem_of_mem (hQ.cover x hx)
    have hp := hQ.after i hi (by rw [hQi]; exact hxr)
    rw [hQi] at hp
    exact hQ.lt _ (List.mem_of_mem_take hp)
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, m0, euPtr, evPtr, qPtr, parPtr, r, θ, base, rfl,
    rfl, fun a ha => ?_, ?_, fun Q' hQ' hQat' => ?_, fun x hx hxr => ?_, fun x hx hxr => ?_, ?_,
    ?_, fun x hx => ?_⟩ ?_
  · show mem₅ a = mem a
    rw [hfr₅ a (by omega), hfr₄ a (by omega), hfr₃ a (by omega), hfr₂ a (by omega),
      hfr₁ a (by omega)]
    rfl
  · intro x hx
    show mem₅ (base + x) = _ ∧ mem₅ (base + 1 * n + x) = _
    rw [hA0 _ (by omega), hA0 _ (by omega)]
    exact hD₁ x hx
  · rw [topDownOrder_eq_of_listAt hQ hQ' hQat hQat']
    refine ⟨?_, ?_⟩
    · have h1 := greedyState_congr_input hQ₁ (par' := fun x => mem (parPtr + x))
        (ν' := fun x => mem₅ (base + 1 * n + x)) hp₁ (fun x hx => (hA0 _ (by omega)).symm) hG
      exact greedyState_congr hQ (fun u hu => (hA2 _ (by omega)).symm)
        (fun u hu => (hA2 _ (by omega)).symm) (fun u hu => (hA2 _ (by omega)).symm)
        (fun u hu => (hA2 _ (by omega)).symm) h1
    · exact closureState_congr_input hQ₄ hp₄ (fun x hx => (hA8 _ (by omega)).symm) hC
  · refine labelRule_congr hx (by have := hparlt x hx hxr; rw [← hp₂ x hx] at this; exact this)
      (fun y hy => ⟨hp₂ y hy, (hA2 _ (by omega)).symm, (hA2 _ (by omega)).symm,
        (hA6 _ (by omega)).symm, (hA6 _ (by omega)).symm⟩) (hL₃ x hx hxr)
  · show mem₅ _ = markVal θ (mem₅ _) (mem₅ _)
    rw [hA8 _ (by omega), hA6 _ (by omega), hA6 _ (by omega)]
    exact hS₄ x hx hxr
  · show mem₅ _ = rootMarkVal θ (mem₅ _) (mem₅ _) _
    rw [hA8 _ (by omega), hA6 _ (by omega), hA6 _ (by omega), hSr₄]
    congr 1
    exact rootFlag_congr hrn (fun y hy => ⟨hp₃ y hy, (hA6 _ (by omega)).symm,
      (hA6 _ (by omega)).symm⟩)
  · show mem₅ _ = closureIn (mem₅ _) (mem₅ _)
    rw [hCr, hA8 (base + 8 * n + r) (by omega)]
  · show mem₅ _ < n ∧ mem₅ _ < n
    rw [hA6 _ (by omega), hA6 _ (by omega)]
    exact hLlt x hx
  · simp [decompWTContract, decompDegContract, decompGreedyContract, decompLabelContract,
      decompMarkContract, decompClosureContract, hargs, argsSize, Expr.size]
    omega

end

end MinCostFlow.LSF.Program
