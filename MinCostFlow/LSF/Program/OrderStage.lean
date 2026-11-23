module

public import MinCostFlow.LSF.Program.EndpointIdx
public import MinCostFlow.LSF.Program.CongOrder
public import MinCostFlow.LSF.Program.UpMin

/-!
# The order `π` and the jump minima, in one procedure

`orderStageProc` makes the edge order `π` of `T₀` and the table that `AuxAt` asks for:
1. `endpointIdxProc` writes, for each edge of `G₀`, the indices in `vList` of its ends;
2. `congOrderProc` sorts the tree edges by their floored congestion and writes the rank of each
   tree edge into the `π` array;
3. `upMinProc` fills the table of the `π`-first edge of each jump.

`orderStage_meetsContract` states the result with the ends in the form of `endpointIdx_spec`,
the sorted list `S` of `congOrderContract` and the table of `upMinContract`. These are the
inputs of `congOrder_isApproxCongOrder` and `auxAt_init`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num MinCostFlow.DynSpanner.Program

@[expose] public section

/-- `liftMin` depends only on the table below `n` and `L`, on the parent edges below `n`, and on
the order of the parent edges. -/
lemma liftMin_congr_all {U U' : ℕ → ℕ → ℕ} {pe pe' piv piv' : ℕ → ℕ} {r n L tM : ℕ}
    (hUU : ∀ i < n, ∀ j < L, U i j = U' i j) (hU : ∀ i < n, ∀ j < L, U i j < n)
    (hpe : ∀ i < n, pe i = pe' i) (hpelt : ∀ i < n, pe i < tM)
    (hpiv : ∀ t < tM, piv t = piv' t) :
    ∀ j ≤ L, ∀ i < n, liftMin U pe piv r i j = liftMin U' pe' piv' r i j ∧
      liftMin U pe piv r i j < tM := by
  intro j
  induction j with
  | zero => intro _ i hi; exact ⟨hpe i hi, hpelt i hi⟩
  | succ j ih =>
    intro hj i hi
    have hUi := hU i hi j (by omega)
    obtain ⟨e1, l1⟩ := ih (by omega) i hi
    obtain ⟨e2, l2⟩ := ih (by omega) _ hUi
    simp only [liftMin]
    rw [← hUU i hi j (by omega), ← e1, ← e2, ← hpiv _ l1, ← hpiv _ l2]
    split_ifs <;> first | exact ⟨rfl, l1⟩ | exact ⟨rfl, l2⟩

/-- Args: `[n, r, m0, eListPtr, tsPtr, hsPtr, i2ePtr, vIdxPtr, euPtr, evPtr, qPtr, Kq, dPtr, K,
tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr, minPtr]`. -/
def orderStageProc (bE bC bM : ℕ) : Stmt :=
  .call 25 bE [.reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9] ;;
  .call 25 bC [.reg 0, .reg 1, .reg 2, .reg 8, .reg 9, .reg 10, .reg 11, .reg 12, .reg 13,
    .reg 14, .reg 15, .reg 16, .reg 17, .reg 18, .reg 19, .reg 20, .reg 21, .reg 22, .reg 23] ;;
  .call 25 bM [.reg 0, .reg 15, .reg 1, .reg 16, .reg 20, .reg 23, .reg 24] ;;
  .ret (.const 0)

lemma orderStageProc_noRand (bE bC bM : ℕ) : (orderStageProc bE bC bM).NoRand := by
  simp [orderStageProc, Stmt.NoRand]

/-- The contract of `orderStageProc`. The graph `G₀` and its edge list lie below the `π` array;
the other inputs lie above it and below the scratch of `congOrderProc` at `dPtr`. -/
def orderStageContract (w h : ℕ) (G₀ : MGraph) (vList eList : List ℕ) : Contract where
  pre args mem := ∃ (n r m0 eListPtr vIdxPtr euPtr evPtr qPtr Kq dPtr K tmpPtr L upPtr depPtr
      parPtr qOrdPtr peBase arrPtr scratchPtr piPtr minPtr tM g0Ptr vCap0 eCap0 : ℕ)
      (tl hd : ℕ → ℕ) (Q : List ℕ),
    args = [n, r, m0, eListPtr, dgETailSlotBase g0Ptr vCap0 eCap0,
      dgEHeadSlotBase g0Ptr vCap0 eCap0, dgIntToExtBase g0Ptr vCap0, vIdxPtr, euPtr, evPtr, qPtr,
      Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr,
      minPtr] ∧
    DynGraphAt mem g0Ptr vCap0 eCap0 G₀ ∧ ListAt mem eListPtr eList ∧ eList.length = m0 ∧
    (∀ e ∈ eList, e ∈ G₀.E) ∧ (∀ i (hi : i < vList.length), mem (vIdxPtr + vList[i]) = i + 1) ∧
    (∀ u ∈ G₀.V, u ∈ vList) ∧ n = vList.length ∧
    0 < h ∧ 2 * h + 2 ≤ w ∧ 16 ≤ 2 ^ w ∧ 1 ≤ K ∧ Kq ≤ K ∧ 0 < n ∧ r < n ∧
    RootedArrays n tM r tl hd (fun x => mem (parPtr + x)) (fun x => mem (peBase + x))
      (fun x => mem (depPtr + x)) ∧ mem (peBase + r) < tM ∧
    TopDownOrder n r (fun x => mem (parPtr + x)) Q ∧ ListAt mem qOrdPtr Q ∧
    LcaTables w n L upPtr depPtr parPtr (fun x => mem (parPtr + x))
      (fun x => mem (depPtr + x)) mem ∧
    (∀ t < m0, Valid mem (qPtr + t * Kq) h Kq) ∧
    ∑ t ∈ Finset.range m0, unsignedVal mem (qPtr + t * Kq) h Kq < capacity h K ∧
    g0Ptr + dynGraphSize vCap0 eCap0 ≤ piPtr ∧ eListPtr + m0 ≤ piPtr ∧ piPtr + tM ≤ vIdxPtr ∧
    vIdxPtr + vCap0 ≤ euPtr ∧ vIdxPtr ≤ qPtr ∧ vIdxPtr ≤ upPtr ∧ vIdxPtr ≤ depPtr ∧
    vIdxPtr ≤ parPtr ∧ vIdxPtr ≤ qOrdPtr ∧ vIdxPtr ≤ peBase ∧
    (qPtr + m0 * Kq ≤ euPtr ∨ evPtr + m0 ≤ qPtr) ∧ (upPtr + n * L ≤ euPtr ∨ evPtr + m0 ≤ upPtr) ∧
    (depPtr + n ≤ euPtr ∨ evPtr + m0 ≤ depPtr) ∧ (parPtr + n ≤ euPtr ∨ evPtr + m0 ≤ parPtr) ∧
    (qOrdPtr + n ≤ euPtr ∨ evPtr + m0 ≤ qOrdPtr) ∧ (peBase + n ≤ euPtr ∨ evPtr + m0 ≤ peBase) ∧
    euPtr + m0 ≤ evPtr ∧ evPtr + m0 ≤ dPtr ∧ qPtr + m0 * Kq ≤ dPtr ∧
    upPtr + n * L ≤ dPtr ∧ depPtr + n ≤ dPtr ∧ parPtr + n ≤ dPtr ∧ qOrdPtr + n ≤ dPtr ∧
    peBase + n ≤ dPtr ∧ dPtr + n * K ≤ tmpPtr ∧ tmpPtr + K ≤ arrPtr ∧
    arrPtr + n ≤ scratchPtr ∧ scratchPtr + n < 2 ^ w ∧
    upPtr + n * L ≤ minPtr ∧ peBase + n ≤ minPtr ∧ piPtr + tM ≤ minPtr ∧
    (minPtr + n * L ≤ euPtr ∨ scratchPtr + n ≤ minPtr) ∧
    (minPtr + n * L ≤ qPtr ∨ qPtr + m0 * Kq ≤ minPtr) ∧ minPtr + n * L < 2 ^ w
  post args mem ret mem' := ∃ (n r m0 eListPtr vIdxPtr euPtr evPtr qPtr Kq dPtr K tmpPtr L upPtr
      depPtr parPtr qOrdPtr peBase arrPtr scratchPtr piPtr minPtr g0Ptr vCap0 eCap0 : ℕ),
    args = [n, r, m0, eListPtr, dgETailSlotBase g0Ptr vCap0 eCap0,
      dgEHeadSlotBase g0Ptr vCap0 eCap0, dgIntToExtBase g0Ptr vCap0, vIdxPtr, euPtr, evPtr, qPtr,
      Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr,
      minPtr] ∧ ret = 0 ∧
    (∀ t < eList.length, mem' (euPtr + t) < vList.length ∧
      vList.getD (mem' (euPtr + t)) 0 = G₀.tail (eList.getD t 0)) ∧
    (∀ t < eList.length, mem' (evPtr + t) < vList.length ∧
      vList.getD (mem' (evPtr + t)) 0 = G₀.head (eList.getD t 0)) ∧
    (∃ S : List ℕ, S.Nodup ∧ S.length = n - 1 ∧ (∀ y, y ∈ S ↔ y < n ∧ y ≠ r) ∧
      S.Pairwise (fun a c =>
        congKey (fun x => mem (parPtr + x)) (fun x => mem (depPtr + x))
          (fun t => mem' (euPtr + t)) (fun t => mem' (evPtr + t))
          (fun t => unsignedVal mem (qPtr + t * Kq) h Kq) m0 a ≤
        congKey (fun x => mem (parPtr + x)) (fun x => mem (depPtr + x))
          (fun t => mem' (euPtr + t)) (fun t => mem' (evPtr + t))
          (fun t => unsignedVal mem (qPtr + t * Kq) h Kq) m0 c) ∧
      ∀ k (hk : k < S.length), mem' (piPtr + mem (peBase + S[k])) = k) ∧
    (∀ i < n, ∀ j < L, mem' (minPtr + (i * L + j)) =
      liftMin (fun i j => mem (upPtr + (i * L + j))) (fun x => mem (peBase + x))
        (fun x => mem' (piPtr + x)) r i j) ∧
    ∀ a, (a < euPtr ∨ evPtr + m0 ≤ a) → (a < dPtr ∨ scratchPtr + n ≤ a) →
      (a < minPtr ∨ minPtr + n * L ≤ a) →
      (∀ y < n, y ≠ r → a ≠ piPtr + mem (peBase + y)) → mem' a = mem a
  cost args _ :=
    let n := args.getD 0 0
    let K := args.getD 13 0
    50 * args.getD 2 0 + args.getD 2 0 * (100 * args.getD 15 0 + 300 * K + 420) +
      (90 * K + 180) * n * (Nat.clog 2 n + 1) + 80 * n * K + 200 * n + 400 +
      100 * n * args.getD 15 0 + 40 * args.getD 15 0 + 200

set_option maxHeartbeats 3200000 in
theorem orderStage_meetsContract {w h : ℕ} {G₀ : MGraph} {vList eList : List ℕ} {p : Program}
    {b bE bC bM : ℕ}
    (hp : p.procs[b]? = some (orderStageProc bE bC bM))
    (hE : MeetsContract w p bE (endpointIdxContract w))
    (hC : MeetsContract w p bC (congOrderContract w h))
    (hM : MeetsContract w p bM (upMinContract w)) :
    MeetsContract w p b (orderStageContract w h G₀ vList eList) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, r, m0, eListPtr, vIdxPtr, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr,
    parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr, minPtr, tM, g0Ptr, vCap0, eCap0, tl, hd, Q,
    rfl, hdg, heAt, heLen, heSub, hvIdx, hVsub, hn, hh0, hw2h, hw16, hK1, hKq, hn0, hrn, hR, hper,
    hQ, hQat,
    hLca, hqV, hqS, hl1, hl2, hl3, hl4, hl5, hl6, hl7, hl8, hl9, hl10, hd1, hd2, hd3, hd4, hd5,
    hd6, hl11, hl12, hl13, hl14, hl15, hl16, hl17, hl18, hl19, hl20, hl21, hl22, hl23, hl24, hl25,
    hl26, hl27, hl28⟩ := hpre
  set args := [n, r, m0, eListPtr, dgETailSlotBase g0Ptr vCap0 eCap0,
      dgEHeadSlotBase g0Ptr vCap0 eCap0, dgIntToExtBase g0Ptr vCap0, vIdxPtr, euPtr, evPtr, qPtr,
      Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr,
      minPtr] with hargs
  have hR0 : ∀ i < 25, (startState args mem pos).regs i = args.getD i 0 := by
    intro i hi
    interval_cases i <;> simp [startState, hargs]
  have hwa : ∀ i < 25, args.getD i 0 < 2 ^ w := fun i hi => hwords _ (by
    simp only [hargs]; interval_cases i <;> simp)
  have hL1 := hLca.hL
  -- reads of the end arrays
  have hdg' := hdg
  obtain ⟨hGv, hVlt, hElt, -, -, -, -, -, -, hext, -, -, -, hslot, -⟩ := hdg'
  have hEm : ∀ t < m0, mem (eListPtr + t) ∈ G₀.E := fun t ht => by
    rw [heAt t (by omega)]; exact heSub _ (List.getElem_mem _)
  have hsizes : ∀ t < m0, mem (eListPtr + t) < eCap0 := fun t ht => hElt _ (hEm t ht)
  have hsV : ∀ t < m0,
      mem (dgETailSlotBase g0Ptr vCap0 eCap0 + mem (eListPtr + t)) < vCap0 ∧
      mem (dgEHeadSlotBase g0Ptr vCap0 eCap0 + mem (eListPtr + t)) < vCap0 := fun t ht => by
    obtain ⟨h1, h2⟩ := hslot _ (hEm t ht)
    obtain ⟨hu, hv⟩ := hGv _ (hEm t ht)
    rw [h1, h2]
    exact ⟨hVlt _ (hext _ hu).1, hVlt _ (hext _ hv).1⟩
  have hiV : ∀ t < m0,
      slotVert mem eListPtr (dgETailSlotBase g0Ptr vCap0 eCap0) (dgIntToExtBase g0Ptr vCap0) t ∈
        G₀.V ∧
      slotVert mem eListPtr (dgEHeadSlotBase g0Ptr vCap0 eCap0) (dgIntToExtBase g0Ptr vCap0) t ∈
        G₀.V := fun t ht => by
    have hs := slotVert_dynGraph hdg heAt heSub (show t < eList.length by omega)
    rw [hs.1, hs.2]
    have he : eList.getD t 0 ∈ G₀.E := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact heSub _ (List.getElem_mem _)
    exact hGv _ he
  have hvw : ∀ u ∈ G₀.V, mem (vIdxPtr + u) ≤ n := fun u hu => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hVsub u hu)
    rw [hvIdx i hi]; omega
  have hnw : n < 2 ^ w := hwa 0 (by omega)
  refine runs_start_le ?_
  unfold orderStageProc
  have r0 := hR0 0 (by omega)
  have r1 := hR0 1 (by omega)
  have r2 := hR0 2 (by omega)
  have r3 := hR0 3 (by omega)
  have r4 := hR0 4 (by omega)
  have r5 := hR0 5 (by omega)
  have r6 := hR0 6 (by omega)
  have r7 := hR0 7 (by omega)
  have r8 := hR0 8 (by omega)
  have r9 := hR0 9 (by omega)
  have r10 := hR0 10 (by omega)
  have r11 := hR0 11 (by omega)
  have r12 := hR0 12 (by omega)
  have r13 := hR0 13 (by omega)
  have r14 := hR0 14 (by omega)
  have r15 := hR0 15 (by omega)
  have r16 := hR0 16 (by omega)
  have r17 := hR0 17 (by omega)
  have r18 := hR0 18 (by omega)
  have r19 := hR0 19 (by omega)
  have r20 := hR0 20 (by omega)
  have r21 := hR0 21 (by omega)
  have r22 := hR0 22 (by omega)
  have r23 := hR0 23 (by omega)
  have r24 := hR0 24 (by omega)
  -- 1. the ends of the edges
  refine runs_seq_call_le (vs := [m0, eListPtr, dgETailSlotBase g0Ptr vCap0 eCap0,
      dgEHeadSlotBase g0Ptr vCap0 eCap0, dgIntToExtBase g0Ptr vCap0, vIdxPtr, euPtr, evPtr]) hE
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 2 (by omega)
      · exact hwa 3 (by omega)
      · exact hwa 4 (by omega)
      · exact hwa 5 (by omega)
      · exact hwa 6 (by omega)
      · exact hwa 7 (by omega)
      · exact hwa 8 (by omega)
      · exact hwa 9 (by omega))
    ⟨m0, eListPtr, dgETailSlotBase g0Ptr vCap0 eCap0, dgEHeadSlotBase g0Ptr vCap0 eCap0,
      dgIntToExtBase g0Ptr vCap0, vIdxPtr, euPtr, evPtr, rfl, hw16, by omega, hl11, by omega,
      fun t ht => by
        simp only [startState]
        have h1 := hsizes t ht
        have h2 := hsV t ht
        have h3 := hiV t ht
        have h4 := hVlt _ h3.1
        have h5 := hVlt _ h3.2
        have h6 := hvw _ h3.1
        have h7 := hvw _ h3.2
        have b1 : dgETailSlotBase g0Ptr vCap0 eCap0 + eCap0 ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
          simp only [dgETailSlotBase, dynGraphSize]; omega
        have b2 : dgEHeadSlotBase g0Ptr vCap0 eCap0 + eCap0 ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
          simp only [dgEHeadSlotBase, dynGraphSize]; omega
        have b3 : dgIntToExtBase g0Ptr vCap0 + vCap0 ≤ g0Ptr + dynGraphSize vCap0 eCap0 := by
          simp only [dgIntToExtBase, dynGraphSize]; omega
        refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩⟩ ?_
  rintro v₁ mem₁ pos₁ ⟨m0', eListPtr', tsPtr', hsPtr', i2ePtr', vIdxPtr', euPtr', evPtr', heq₁, -,
    hout₁, hfr₁⟩
  simp only [List.cons.injEq, and_true] at heq₁
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₁
  try dsimp only at hout₁ hfr₁
  obtain ⟨heu₁, hev₁⟩ := endpointIdx_spec (mem' := mem₁) hdg heAt heSub hvIdx hVsub
    (fun t ht => hout₁ t (by omega))
  have hE1 : ∀ a, (a < euPtr ∨ evPtr + m0 ≤ a) → mem₁ a = mem a := hfr₁
  have hpar₁ : ∀ x < n, mem (parPtr + x) = mem₁ (parPtr + x) := fun x hx =>
    (hE1 _ (by omega)).symm
  have hpe₁ : ∀ x < n, mem (peBase + x) = mem₁ (peBase + x) := fun x hx =>
    (hE1 _ (by omega)).symm
  have hdep₁ : ∀ x < n, mem (depPtr + x) = mem₁ (depPtr + x) := fun x hx =>
    (hE1 _ (by omega)).symm
  have hR₁ := hR.congr hrn hpar₁ hpe₁ hdep₁
  have hq₁ : ∀ t < m0, ∀ i < Kq, mem (qPtr + t * Kq + i) = mem₁ (qPtr + t * Kq + i) := by
    intro t ht i hi
    have : (t + 1) * Kq ≤ m0 * Kq := Nat.mul_le_mul_right _ ht
    rw [Nat.add_one_mul] at this
    exact (hE1 _ (by omega)).symm
  have hqval : ∀ t < m0, unsignedVal mem (qPtr + t * Kq) h Kq =
      unsignedVal mem₁ (qPtr + t * Kq) h Kq := fun t ht => unsignedVal_congr (hq₁ t ht)
  have hLca₁ : LcaTables w n L upPtr depPtr parPtr (fun x => mem₁ (parPtr + x))
      (fun x => mem₁ (depPtr + x)) mem₁ := by
    have h := hLca.congr hR hpar₁ hdep₁
    refine ⟨h.hL, h.hdep, fun i hi j hj => ?_, fun i hi => ?_, fun i hi => ?_, h.hupW, h.hdW,
      h.hpW⟩
    · have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
      rw [Nat.add_one_mul] at this
      rw [hE1 _ (by omega)]; exact h.hup i hi j hj
    · rfl
    · rfl
  have hQat₁ : ListAt mem₁ qOrdPtr Q := fun i hi => by
    rw [hE1 _ (by rw [hQ.len] at hi; omega)]; exact hQat i hi
  have hends₁ : ∀ t < m0, mem₁ (euPtr + t) < n ∧ mem₁ (evPtr + t) < n := fun t ht =>
    ⟨by have := (heu₁ t (by omega)).1; omega, by have := (hev₁ t (by omega)).1; omega⟩
  have hqV₁ : ∀ t < m0, Valid mem₁ (qPtr + t * Kq) h Kq := fun t ht i hi => by
    rw [← hq₁ t ht i hi]; exact hqV t ht i hi
  have hqS₁ : ∑ t ∈ Finset.range m0, unsignedVal mem₁ (qPtr + t * Kq) h Kq < capacity h K := by
    rw [← Finset.sum_congr rfl fun t ht => hqval t (Finset.mem_range.mp ht)]; exact hqS
  -- 2. the order `π`
  refine runs_seq_call_le (vs := [n, r, m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr,
      depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr]) hC
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))))))))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 2 (by omega)
      · exact hwa 8 (by omega)
      · exact hwa 9 (by omega)
      · exact hwa 10 (by omega)
      · exact hwa 11 (by omega)
      · exact hwa 12 (by omega)
      · exact hwa 13 (by omega)
      · exact hwa 14 (by omega)
      · exact hwa 15 (by omega)
      · exact hwa 16 (by omega)
      · exact hwa 17 (by omega)
      · exact hwa 18 (by omega)
      · exact hwa 19 (by omega)
      · exact hwa 20 (by omega)
      · exact hwa 21 (by omega)
      · exact hwa 22 (by omega)
      · exact hwa 23 (by omega))
    ⟨n, r, m0, euPtr, evPtr, qPtr, Kq, dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr,
      peBase, arrPtr, scratchPtr, piPtr, tM, tl, hd, Q, rfl, hh0, hw2h, hw16, hK1, hKq, hn0, hR₁,
      hQ.congr hpar₁, hQat₁, hLca₁, hends₁, hqV₁, hqS₁,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega), by omega⟩ ?_
  rintro v₂ mem₂ pos₂ ⟨n', r', m0', euPtr', evPtr', qPtr', Kq', dPtr', K', tmpPtr', L', upPtr',
    depPtr', parPtr', qOrdPtr', peBase', arrPtr', scratchPtr', piPtr', S, heq₂, -, hfr₂, hSnd,
    hSlen, hSmem, hSsort, hrank⟩
  simp only [List.cons.injEq, and_true] at heq₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩ := heq₂
  try dsimp only at hfr₂ hrank
  have hpelt : ∀ y < n, mem₁ (peBase + y) < tM := fun y hy => by
    by_cases hyr : y = r
    · rw [hyr, ← hpe₁ r hrn]; exact hper
    · exact (hR₁.step y hy hyr).1
  have hE2 : ∀ a, (a < dPtr ∨ scratchPtr + n ≤ a) → (a < piPtr ∨ piPtr + tM ≤ a) →
      mem₂ a = mem₁ a := fun a ha hpi => hfr₂ a ha fun y hy _ => by
    have := hpelt y hy; omega
  have hup₂ : ∀ i < n, ∀ j < L, mem₂ (upPtr + (i * L + j)) = mem (upPtr + (i * L + j)) := by
    intro i hi j hj
    have : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right _ hi
    rw [Nat.add_one_mul] at this
    rw [hE2 _ (by omega) (by omega), hE1 _ (by omega)]
  have hpe₂ : ∀ x < n, mem₂ (peBase + x) = mem (peBase + x) := fun x hx => by
    rw [hE2 _ (by omega) (by omega), hpe₁ x hx]
  have hUlt : ∀ i < n, ∀ j < L, mem₂ (upPtr + (i * L + j)) < n := fun i hi j hj => by
    rw [hup₂ i hi j hj, hLca.hup i hi j hj]
    exact liftF_lt hR.par_lt j i hi
  have hpiLt : ∀ i < n, piPtr + mem₂ (peBase + i) < minPtr := fun i hi => by
    rw [hpe₂ i hi, hpe₁ i hi]; have := hpelt i hi; omega
  -- 3. the jump minima
  refine runs_seq_call_le (vs := [n, L, r, upPtr, peBase, piPtr, minPtr]) hM
    (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
      (evalArgs_cons (by eval_expr) (evalArgs_nil _ _))))))))
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hwa 0 (by omega)
      · exact hwa 15 (by omega)
      · exact hwa 1 (by omega)
      · exact hwa 16 (by omega)
      · exact hwa 20 (by omega)
      · exact hwa 23 (by omega)
      · exact hwa 24 (by omega))
    ⟨n, L, r, upPtr, peBase, piPtr, minPtr, rfl, hw16, hL1, hUlt, by omega, by omega,
      hpiLt, by omega⟩ ?_
  rintro v₃ mem₃ pos₃ ⟨n', L', r', upPtr', peBase', piPtr', minPtr', heq₃, -, hmin₃, hfr₃⟩
  simp only [List.cons.injEq, and_true] at heq₃
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq₃
  try dsimp only at hmin₃ hfr₃
  have hE3 : ∀ a, (a < minPtr ∨ minPtr + n * L ≤ a) → mem₃ a = mem₂ a := hfr₃
  have hpi₃ : ∀ t < tM, mem₃ (piPtr + t) = mem₂ (piPtr + t) := fun t ht => hE3 _ (by omega)
  have hends₃ : ∀ t < m0, mem₃ (euPtr + t) = mem₁ (euPtr + t) ∧
      mem₃ (evPtr + t) = mem₁ (evPtr + t) := fun t ht =>
    ⟨by rw [hE3 _ (by omega), hE2 _ (by omega) (by omega)],
      by rw [hE3 _ (by omega), hE2 _ (by omega) (by omega)]⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, r, m0, eListPtr, vIdxPtr, euPtr, evPtr, qPtr, Kq,
    dPtr, K, tmpPtr, L, upPtr, depPtr, parPtr, qOrdPtr, peBase, arrPtr, scratchPtr, piPtr, minPtr,
    g0Ptr, vCap0, eCap0, rfl, rfl, fun t ht => ?_, fun t ht => ?_, ⟨S, hSnd, hSlen, hSmem, ?_, ?_⟩,
    fun i hi j hj => ?_, fun a ha1 ha2 ha3 ha4 => ?_⟩ ?_
  · try dsimp only
    rw [(hends₃ t (by omega)).1]; exact heu₁ t ht
  · try dsimp only
    rw [(hends₃ t (by omega)).2]; exact hev₁ t ht
  · -- the sorted list
    try dsimp only
    refine hSsort.imp fun {a c} hac => ?_
    have hc := fun y => congKey_congr hR₁ (m0 := m0) (fun x hx => (hpar₁ x hx).symm)
      (fun x hx => (hdep₁ x hx).symm)
      (fun t ht => ⟨by have := (heu₁ t (by omega)).1; omega,
        by have := (hev₁ t (by omega)).1; omega⟩)
      (fun t ht => ((hends₃ t ht).1).symm) (fun t ht => ((hends₃ t ht).2).symm)
      (fun t ht => (hqval t ht).symm) y
    rw [← hc a, ← hc c]
    exact hac
  · -- the ranks
    intro k hk
    try dsimp only
    have hy : S[k] < n ∧ S[k] ≠ r := (hSmem _).mp (List.getElem_mem hk)
    rw [hpe₁ _ hy.1, hpi₃ _ (hpelt _ hy.1)]
    exact hrank k hk
  · -- the table
    try dsimp only
    rw [hmin₃ i hi j hj]
    exact ((liftMin_congr_all (tM := tM) hup₂ hUlt hpe₂ (fun i hi => by
      rw [hpe₂ i hi, hpe₁ i hi]; exact hpelt i hi)
      (fun t ht => (hpi₃ t ht).symm)) j (by omega) i hi).1
  · -- the frame
    try dsimp only
    rw [hE3 a ha3, hfr₂ a ha2 (fun y hy hyr => by rw [← hpe₁ y hy]; exact ha4 y hy hyr)]
    exact hE1 a ha1
  · -- the cost
    simp only [orderStageContract, endpointIdxContract, congOrderContract, upMinContract,
      argsSize, Expr.size_const, Expr.size_reg, List.sum_cons, List.sum_nil, List.map_cons,
      List.map_nil, List.getD_cons_zero, List.getD_cons_succ, hargs]
    omega

end

end MinCostFlow.LSF.Program
