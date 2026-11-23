module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBucket
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import MinCostFlow.Num.DivisionSigns
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The bucket table of the init (`AssemblyFirstInitBktTable`)

The bundle side of a branch keeps an array from edges to the words of their buckets
(`AsmSdMapsAt`, `AssemblyBranchSide.lean`): for each edge `e` of `G₀`, the word
`bucketCode (origBucket e)`, where `origBucket e = bucketOf (wstr e · ℓ₀ e)` at the init. This file
writes that array.

The procedure `bucketTableBody` walks the list of the edges of `G` in its memory form
(`DynGraphAt`). For the edge `e` it calls the bucket word (`bucketWordBody`,
`AssemblyFirstInitBucket.lean`) on the two blocks of `wstr e = num e / den e` in P4's export and
the block of `ℓ₀ e` in the lengths, and stores the result at `bktH + e`. Each call gets fresh
scratch memory of its own, `bucketWordSpace L_w L` words, after the scratch of the call before. So
the array is written in `G.m` calls, and the procedure returns the end of the scratch.

The main result is `bucketTable_runs`. Then `bucketTable_origBucket` gives the clause of
`AsmSdMapsAt` on the edges, at the bundle state of the init, and `bucketCode_blocks_le` bounds
each word, so that the array holds words.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program MinCostFlow.Chain
open MinCostFlow.Bundle MinCostFlow.LSF MinCostFlow.DynSpanner

/-! ## The procedure -/

/-- One step of the loop over the edges: register `15` holds the index `i`, and the edge
`e = eL[i]` goes to register `16`. Call the bucket word on `num e`, `den e`, `ℓ₀ e`, with scratch
from `heap + i · S`, and store the result at `bktH + e`. -/
def bucketTableStep (fBkt : ℕ) : Stmt :=
  .assign 16 (.load (.bin .add (.reg 10) (.reg 15))) ;;
  .call 17 fBkt [.bin .add (.reg 11) (.bin .mul (.reg 16) (.reg 13)),
    .bin .add (.reg 12) (.bin .mul (.reg 16) (.reg 13)), .reg 13,
    .bin .add (.reg 2) (.bin .mul (.reg 16) (.reg 3)), .reg 3, .reg 4,
    .bin .add (.reg 6) (.bin .mul (.reg 15) (.reg 14))] ;;
  .store (.bin .add (.reg 5) (.reg 16)) (.reg 17)

/-- **The bucket table**, `[graph, expPtr, lengths, L, P, bktH, heap]`. Registers: `7 = vCap`,
`8 = eCap`, `9 = m`, `10` the start of the edge list of `G`, `11 = numPtr`, `12 = denPtr`,
`13 = L_w` (from P4's export at `expPtr`), `14 = S = bucketWordSpace L_w L`. For each edge of the
edge list, in order, it stores the bucket word of the edge at `bktH + e`
(`bucketTableStep`). It returns `heap + m · S`. -/
def bucketTableBody (fBkt : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 1))) ;;
  .assign 9 (.load (.bin .add (.reg 0) (.const 3))) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 0) (.const 4))
    (.bin .mul (.const 7) (.reg 7))) (.reg 8)) ;;
  .assign 11 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 12 (.load (.bin .add (.reg 1) (.const 5))) ;;
  .assign 13 (.load (.bin .add (.reg 1) (.const 6))) ;;
  .assign 14 (.bin .add (.bin .add (.bin .mul (.const 21) (.reg 13))
    (.bin .mul (.const 16) (.reg 3))) (.const 20)) ;;
  forRange 15 (.const 0) (.reg 9) (bucketTableStep fBkt) ;;
  .ret (.bin .add (.reg 6) (.bin .mul (.reg 9) (.reg 14)))

/-- The procedure and the bucket word with its modules, from `b` on (`17` bodies). -/
def bucketTableModule (b : ℕ) : List Stmt :=
  bucketTableBody (b + 1) :: bucketWordModule (b + 1)

theorem bucketTableBody_noRand (fBkt : ℕ) : (bucketTableBody fBkt).NoRand := by
  simp [bucketTableBody, bucketTableStep, forRange, forUp, Stmt.NoRand]

theorem bucketTableModule_noRand (b : ℕ) : ∀ s ∈ bucketTableModule b, s.NoRand := by
  intro s hs
  simp only [bucketTableModule, List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact bucketTableBody_noRand _
  · exact bucketWordModule_noRand _ s hs

/-- The cost of the bucket table on `m` edges. -/
def bucketTableCost (Lw L m : ℕ) : ℕ := m * (bucketWordCost Lw L + 60) + 150

/-! ## The size of a bucket word -/

/-- **The bucket word is small.** On valid blocks with `0 < den` and `0 < len`, the code of the
bucket of `num / den · len / 2 ^ P` is at most `2 (8 L_w + 4 L + P + 1)`: the floor of `log₂` of
`|num| · len` is below `4 L_w + 4 L`, and that of `den` is below `4 L_w`. -/
theorem bucketCode_blocks_le {mem : ℕ → ℕ} {numA denA lenA Lw L P : ℕ}
    (hvn : Num.Valid mem numA 4 Lw) (hvd : Num.Valid mem denA 4 Lw)
    (hvl : Num.Valid mem lenA 4 L) (hd0 : 0 < Num.intVal mem denA 4 Lw)
    (hl0 : 0 < Num.intVal mem lenA 4 L) :
    bucketCode (bucketOf ((Num.intVal mem numA 4 Lw : ℝ) / (Num.intVal mem denA 4 Lw : ℝ) *
      Num.fixVal mem lenA 4 L P)) ≤ 2 * (8 * Lw + 4 * L + P + 1) := by
  set num := Num.intVal mem numA 4 Lw with hnum
  set den := Num.intVal mem denA 4 Lw with hden
  set len := Num.intVal mem lenA 4 L with hlen
  set X := num.natAbs * len.toNat with hX
  set a := Nat.log 2 X with ha
  set c := Nat.log 2 den.toNat with hc
  set lt : ℕ := if X * 2 ^ c < den.toNat * 2 ^ a then 1 else 0 with hlt
  have hfix : Num.fixVal mem lenA 4 L P = (len : ℝ) / 2 ^ P := rfl
  rw [hfix, bucketCode_bucketOf_eq (t := if 0 < X then 1 else 0) (a := a) (c := c) (lt := lt)
    hd0 hl0 (by split_ifs <;> simp_all) (fun _ => rfl) rfl rfl]
  have hnumB : num.natAbs < 2 ^ (4 * Lw) := by
    have := Num.intVal_natAbs_lt hvn
    rwa [bucket_capacity_four] at this
  have hdenB : den.toNat < 2 ^ (4 * Lw) := by
    have := Num.intVal_natAbs_lt hvd
    rw [bucket_capacity_four] at this
    omega
  have hlenB : len.toNat < 2 ^ (4 * L) := by
    have := Num.intVal_natAbs_lt hvl
    rw [bucket_capacity_four] at this
    omega
  have hXB : X < 2 ^ (4 * Lw + 4 * L) := by
    rw [pow_add, hX]
    exact Nat.mul_lt_mul'' hnumB hlenB
  have haB : a < 4 * Lw + 4 * L ∨ X = 0 := by
    by_cases hX0 : X = 0
    · exact Or.inr hX0
    · exact Or.inl (Nat.log_lt_of_lt_pow hX0 hXB)
  have hcB : c < 4 * Lw := Nat.log_lt_of_lt_pow (by omega) hdenB
  have hlt1 : lt ≤ 1 := bucket_ite_le_one _ _
  by_cases hX0 : 0 < X
  · simp only [hX0, ↓reduceIte]
    rcases haB with haB | haB
    · split_ifs <;> omega
    · omega
  · simp [hX0]

/-! ## The run -/

private theorem bkt_mem_take_succ {eL : List ℕ} {i : ℕ} (hi : i < eL.length) (e : ℕ) :
    e ∈ eL.take (i + 1) ↔ e ∈ eL.take i ∨ e = eL[i] := by
  rw [List.take_add_one, List.mem_append]
  simp [List.getElem?_eq_getElem hi]

private theorem bkt_not_mem_take {eL : List ℕ} {i : ℕ} (hnd : eL.Nodup) (hi : i < eL.length) :
    eL[i] ∉ eL.take i := by
  intro hm
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hm
  have hj' : j < i := by
    have := List.length_take_le i eL
    simp only [List.length_take] at hj
    omega
  rw [List.getElem_take] at hjv
  have := (List.Nodup.getElem_inj_iff hnd).mp hjv
  omega

/-- **The run of the bucket table.** Let `G` be in memory form at `graph`, P4's export of a state
`cs` with `cs.G = G` at `expPtr`, and the lengths `ℓ₀` of `G` at `lengths`, all below `bktH`, and
let the memory be fresh from `bktH`. Let `L_w` be the limb count of the export and
`S = bucketWordSpace L_w L`. Then the procedure returns `heap + G.m · S`. Afterwards the array at
`bktH` holds, at each edge `e` of `G`, the word `bucketCode (bucketOf (wstr e · ℓ₀ e))`, and `0` at
the other numbers below `eCap`; these are words. The memory below `bktH` and from `bktH + eCap`
below `heap` does not change, the memory is fresh from `heap + G.m · S`, and the cost is at most
`bucketTableCost L_w L G.m`. -/
theorem bucketTable_runs {w b : ℕ} {p : Program} (hw : 10 ≤ w)
    (hp : p.HasAt b (bucketTableModule b)) (ω : ℕ → Bool) {pos : ℕ}
    {graph expPtr expEnd lengths L P bktH heap vCap eCap h₀ L' capExp M N : ℕ} {G : MGraph}
    {cs : CompLSFState} {ℓ₀ : ℕ → ℝ} {mem : ℕ → ℕ}
    (hG : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ bktH)
    (hExp : CompBranchExportAt w mem expPtr expEnd L' capExp M N vCap eCap cs)
    (hcsG : cs.G = G) (hExpLe : expEnd ≤ bktH)
    (hlen : BranchLengthsAt mem lengths eCap L P h₀ G ℓ₀) (hh₀ : h₀ ≤ bktH)
    (hbkt : bktH + eCap ≤ heap) (hz : ZeroFrom mem bktH)
    (hsp : heap + G.m * bucketWordSpace (mem (expPtr + 6)) L < 2 ^ w)
    (hPw : 2 * (P + bucketWordSpace (mem (expPtr + 6)) L) < 2 ^ w) :
    ∃ st' c, Runs w p ω (bucketTableBody (b + 1))
        (startState [graph, expPtr, lengths, L, P, bktH, heap] mem pos)
        (.returned (heap + G.m * bucketWordSpace (mem (expPtr + 6)) L)) st' c ∧
      (∀ e ∈ G.E, st'.mem (bktH + e) = bucketCode (bucketOf (cs.lsf.wstr e * ℓ₀ e))) ∧
      (∀ e < eCap, e ∉ G.E → st'.mem (bktH + e) = 0) ∧
      (∀ e < eCap, st'.mem (bktH + e) < 2 ^ w) ∧
      (∀ a < bktH, st'.mem a = mem a) ∧
      (∀ a, bktH + eCap ≤ a → a < heap → st'.mem a = mem a) ∧
      ZeroFrom st'.mem (heap + G.m * bucketWordSpace (mem (expPtr + 6)) L) ∧
      c ≤ bucketTableCost (mem (expPtr + 6)) L G.m := by
  -- the facts of the inputs
  obtain ⟨hGval, hVlt, hElt, hmVCap, hmECap, -, hmM, -, -, -, -, -,
    ⟨eL, heLen, heNd, heMem, heLA, -⟩, -, -⟩ := hG
  obtain ⟨hexpE, -, -, -, -, -, -, -, -, -, -, -, num, den, hnd⟩ := hExp
  set Lw := mem (expPtr + 6) with hLw
  set numPtr := mem (expPtr + 4) with hnumPtr
  set denPtr := mem (expPtr + 5) with hdenPtr
  set S := bucketWordSpace Lw L with hS
  set m := G.m with hm
  set eLB := dgEListBase graph vCap eCap with heLB
  have hdg : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hSdef : S = 21 * Lw + 16 * L + 20 := by simp only [hS, bucketWordSpace]; ring
  have hw1 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hheap : heap < 2 ^ w := by omega
  have hm_le : m ≤ eCap := by
    calc m = eL.length := heLen.symm
      _ = eL.toFinset.card := (List.toFinset_card_of_nodup heNd).symm
      _ ≤ (Finset.range eCap).card := Finset.card_le_card fun x hx =>
          Finset.mem_range.mpr (hElt x ((heMem x).mp (List.mem_toFinset.mp hx)))
      _ = eCap := Finset.card_range eCap
  have hlenB : lengths + eCap * L ≤ bktH := le_trans hlen.1 hh₀
  have heLBle : eLB + eCap ≤ bktH := by simp only [heLB, dgEListBase]; omega
  -- the word of an edge, in the original memory
  let code : ℕ → ℕ := fun e => bucketCode (bucketOf (cs.lsf.wstr e * ℓ₀ e))
  have hcsE : ∀ e ∈ G.E, e ∈ cs.G.E := fun e he => hcsG ▸ he
  -- the invariant of the loop
  let Inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = graph ∧ st.regs 1 = expPtr ∧ st.regs 2 = lengths ∧ st.regs 3 = L ∧
    st.regs 4 = P ∧ st.regs 5 = bktH ∧ st.regs 6 = heap ∧ st.regs 9 = m ∧ st.regs 10 = eLB ∧
    st.regs 11 = numPtr ∧ st.regs 12 = denPtr ∧ st.regs 13 = Lw ∧ st.regs 14 = S ∧
    st.regs 15 = i ∧
    (∀ a < bktH, st.mem a = mem a) ∧
    (∀ e < eCap, st.mem (bktH + e) = if e ∈ eL.take i then code e else 0) ∧
    (∀ a, bktH + eCap ≤ a → a < heap → st.mem a = mem a) ∧
    ZeroFrom st.mem (heap + i * S)
  have hcodeB : ∀ e ∈ G.E, code e ≤ 2 * (P + S) := by
    intro e he
    obtain ⟨hnLo, hnHi, hdLo, hdHi, hnV, hdV, hnEq, hdEq, hdPos, hrat⟩ := hnd e (hcsE e he)
    have hlp := branchLengthsAt_intVal_pos hlen he
    have hb := bucketCode_blocks_le (P := P) hnV hdV hlp.1 (by rw [hdEq]; exact hdPos) hlp.2
    rw [bucketWord_edge hlen he hnEq hdEq hrat] at hb
    have : 2 * (8 * Lw + 4 * L + P + 1) ≤ 2 * (P + S) := by rw [hSdef]; omega
    exact le_trans hb this
  -- one step of the loop
  have hstep : ∀ i, 0 ≤ i → i < m →
      Triple w p (Inv i) (bucketTableStep (b + 1))
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs 15 (i + 1) } ∧
            st₁.regs 15 = i)
        (fun _ => bucketWordCost Lw L + 50) := by
    intro i _ hi st ω' hI
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r9, r10, r11, r12, r13, r14, r15, hlow, htbl, hmid,
      hzf⟩ := hI
    have hiL : i < eL.length := by omega
    set e := eL[i] with he_def
    have heG : e ∈ G.E := (heMem e).mp (List.getElem_mem hiL)
    have heC : e < eCap := hElt e heG
    obtain ⟨hnLo, hnHi, hdLo, hdHi, hnV, hdV, hnEq, hdEq, hdPos, hrat⟩ := hnd e (hcsE e heG)
    have hlp := branchLengthsAt_intVal_pos hlen heG
    have hnHi' : numPtr + e * Lw + Lw ≤ bktH := by
      have : (e + 1) * Lw = e * Lw + Lw := Nat.add_one_mul e Lw
      omega
    have hdHi' : denPtr + e * Lw + Lw ≤ bktH := by
      have : (e + 1) * Lw = e * Lw + Lw := Nat.add_one_mul e Lw
      omega
    have hlHi : lengths + e * L + L ≤ bktH := by
      have h1 : (e + 1) * L ≤ eCap * L := Nat.mul_le_mul_right L (by omega)
      have : (e + 1) * L = e * L + L := Nat.add_one_mul e L
      omega
    have hiS : i * S + S ≤ m * S := by
      have h1 : (i + 1) * S ≤ m * S := Nat.mul_le_mul_right S (by omega)
      have : (i + 1) * S = i * S + S := Nat.add_one_mul i S
      omega
    have hsrc : st.mem (eLB + i) = e := by
      rw [hlow _ (by simp only [heLB, dgEListBase]; omega)]
      exact heLA i hiL
    -- the blocks, in the memory of the step
    have hagN : ∀ j < Lw, st.mem (numPtr + e * Lw + j) = mem (numPtr + e * Lw + j) :=
      fun j hj => hlow _ (by omega)
    have hagD : ∀ j < Lw, st.mem (denPtr + e * Lw + j) = mem (denPtr + e * Lw + j) :=
      fun j hj => hlow _ (by omega)
    have hagL : ∀ j < L, st.mem (lengths + e * L + j) = mem (lengths + e * L + j) :=
      fun j hj => hlow _ (by omega)
    have hcodeE : bucketCode (bucketOf ((Num.intVal st.mem (numPtr + e * Lw) 4 Lw : ℝ) /
        (Num.intVal st.mem (denPtr + e * Lw) 4 Lw : ℝ) *
        Num.fixVal st.mem (lengths + e * L) 4 L P)) = code e := by
      have h1 : Num.intVal st.mem (numPtr + e * Lw) 4 Lw = Num.intVal mem (numPtr + e * Lw) 4 Lw :=
        Num.intVal_congr hagN
      have h2 : Num.intVal st.mem (denPtr + e * Lw) 4 Lw = Num.intVal mem (denPtr + e * Lw) 4 Lw :=
        Num.intVal_congr hagD
      have h3 : Num.fixVal st.mem (lengths + e * L) 4 L P =
          Num.fixVal mem (lengths + e * L) 4 L P := by
        unfold Num.fixVal
        rw [Num.intVal_congr hagL]
      rw [h1, h2, h3]
      exact bucketWord_edge hlen heG hnEq hdEq hrat
    have hcodeW : code e < 2 ^ w := lt_of_le_of_lt (hcodeB e heG) hPw
    have hBC := bucketWord_meetsContract (w := w) (b := b + 1) (p := p) hw
      (Num.hasAt_append_right (xs := [bucketTableBody (b + 1)]) hp)
    refine runs_start_le ?_
    unfold bucketTableStep
    refine runs_seq_assign_le (v := e) (Expr.eval_load_of_eq (by eval_expr) hsrc) ?_
    refine runs_seq_call_le hBC
      (vs := [numPtr + e * Lw, denPtr + e * Lw, Lw, lengths + e * L, L, P, heap + i * S])
      (by eval_expr) (by wram_words) ?_ ?_
    · refine ⟨numPtr + e * Lw, denPtr + e * Lw, Lw, lengths + e * L, L, P, heap + i * S, rfl,
        by omega, by omega, by omega,
        bucket_valid_of_agree hnV hagN, bucket_valid_of_agree hdV hagD,
        bucket_valid_of_agree hlp.1 hagL, ?_, ?_, hzf, by omega, hPw⟩
      · rw [Num.intVal_congr hagD, hdEq]; exact hdPos
      · rw [Num.intVal_congr hagL]; exact hlp.2
    intro v m1 pos1 hpost
    obtain ⟨hf1, hz1, hv1⟩ := hpost
    change ∀ x < heap + i * S, m1 x = st.mem x at hf1
    change ZeroFrom m1 (heap + i * S + S) at hz1
    change v = bucketCode (bucketOf ((Num.intVal st.mem (numPtr + e * Lw) 4 Lw : ℝ) /
      (Num.intVal st.mem (denPtr + e * Lw) 4 Lw : ℝ) *
      Num.fixVal st.mem (lengths + e * L) 4 L P)) at hv1
    rw [hcodeE] at hv1
    subst hv1
    refine runs_store_le (x := bktH + e) (v := code e) (by eval_expr) (by eval_expr) ?_ ?_
    · refine ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
        by simp [r5], by simp [r6], by simp [r9], by simp [r10], by simp [r11], by simp [r12],
        by simp [r13], by simp [r14], by simp, ?_, ?_, ?_, ?_⟩, by simp [r15]⟩
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega), hf1 a (by omega)]
        exact hlow a ha
      · intro e' he'
        dsimp only
        have hiff := bkt_mem_take_succ hiL e'
        by_cases hee : e' = e
        · have hm : e' ∈ List.take (i + 1) eL := hiff.mpr (Or.inr (hee.trans he_def))
          rw [hee, Function.update_self]
          rw [← hee]
          simp only [hm, ↓reduceIte]
        · rw [Function.update_of_ne (by omega), hf1 _ (by omega), htbl e' he']
          simp only [hiff, ← he_def, hee, or_false]
      · intro a ha1 ha2
        dsimp only
        rw [Function.update_of_ne (by omega), hf1 a (by omega)]
        exact hmid a ha1 ha2
      · intro a ha
        dsimp only
        rw [Function.update_of_ne (by omega)]
        have : (i + 1) * S = i * S + S := Nat.add_one_mul i S
        exact hz1 a (by omega)
    · simp only [Expr.size_reg, Expr.size_load, Expr.size_bin, argsSize_cons,
        argsSize_nil, bucketWordContract, List.getD_cons_succ, List.getD_cons_zero]
      omega
  -- the loop
  have hloop := Triple.forRange_const (w := w) (p := p) (r := 15) (lo := .const 0) (hi := .reg 9)
    (body := bucketTableStep (b + 1))
    (P := fun st => Inv 0 { st with regs := Function.update st.regs 15 0 })
    (Inv := Inv) (bucketWordCost Lw L + 50) 0 m (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.2.2.2.1) hstep
  -- the straight-line start
  have hmM' : mem (graph + 3) = m := by simpa [dgMOff] using hmM
  have hmV' : mem graph = vCap := by simpa [dgVCapOff] using hmVCap
  have hmE' : mem (graph + 1) = eCap := by simpa [dgECapOff] using hmECap
  have hgw : graph + 4 + 7 * vCap + 9 * eCap < 2 ^ w := by omega
  have hexpw : expPtr + 8 < 2 ^ w := by omega
  have hLw_le : Lw ≤ S := by omega
  have hmS : m * S ≤ heap + m * S := Nat.le_add_left _ _
  suffices hmain : ∃ o st' c, Runs w p ω (bucketTableBody (b + 1))
      (startState [graph, expPtr, lengths, L, P, bktH, heap] mem pos) o st' c ∧
      (o = .returned (heap + m * S) ∧ Inv m st') ∧ 0 + c ≤ bucketTableCost Lw L m by
    obtain ⟨o, st', c, hrun, ⟨rfl, hI⟩, hc⟩ := hmain
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hlow, htbl, hmid, hzf⟩ := hI
    have htake : eL.take m = eL := List.take_of_length_le (by omega)
    rw [htake] at htbl
    refine ⟨st', c, hrun, fun e he => ?_, fun e he hne => ?_, fun e he => ?_, hlow, hmid, hzf,
      by omega⟩
    · rw [htbl e (hElt e he)]
      simp only [(heMem e).mpr he, ↓reduceIte]
      rfl
    · rw [htbl e he]
      simp only [show e ∉ eL from fun h => hne ((heMem e).mp h), ↓reduceIte]
    · rw [htbl e he]
      split_ifs with h
      · exact lt_of_le_of_lt (hcodeB e ((heMem e).mp h)) hPw
      · exact Nat.two_pow_pos w
  unfold bucketTableBody
  refine runs_seq_assign_le (v := vCap) (Expr.eval_load_of_eq (by eval_expr) hmV') ?_
  refine runs_seq_assign_le (v := eCap) (Expr.eval_load_of_eq (by eval_expr) hmE') ?_
  refine runs_seq_assign_le (v := m) (Expr.eval_load_of_eq (by eval_expr) hmM') ?_
  refine runs_seq_assign_le (v := eLB) (Expr.eval_eq_of_eq (by eval_expr)
    (by simp only [heLB, dgEListBase])) ?_
  refine runs_seq_assign_le (v := numPtr) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := denPtr) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := Lw) (Expr.eval_load_of_eq (by eval_expr) rfl) ?_
  refine runs_seq_assign_le (v := S) (Expr.eval_eq_of_eq (by eval_expr) (by omega)) ?_
  refine runs_seq_triple_le hloop ?_ ?_
  · refine ⟨by simp [startState], by simp [startState], by simp [startState],
      by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp, by simp, by simp, by simp, by simp, by simp, by simp,
      fun a _ => rfl, fun e he => ?_, fun a _ _ => rfl, fun a ha => hz a (by omega)⟩
    simp only [List.take_zero, List.not_mem_nil, ↓reduceIte]
    exact hz _ (by omega)
  intro st₁ hI
  have r6 : st₁.regs 6 = heap := hI.2.2.2.2.2.2.1
  have r9 : st₁.regs 9 = m := hI.2.2.2.2.2.2.2.1
  have r14 : st₁.regs 14 = S := hI.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine runs_ret_le (v := heap + m * S) (by eval_expr) ⟨rfl, hI⟩ ?_
  have hmul : m * (bucketWordCost Lw L + 60) = m * (bucketWordCost Lw L + 50 + 1 + 8) + m := by
    ring
  simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin, bucketTableCost,
    Nat.sub_zero]
  omega

/-! ## The clause of the maps -/

/-- **The bucket of an edge at the init.** At the bundle state of the init, the bucket of an edge
`e` of `G` is the bucket of `wstr e · ℓ₀ e`, where `wstr` is the stretch of the LSF state of the
init (`initBundleTreeWithParams` takes `bucketOf (coreLen cs₀.lsf (safeLen G ℓ₀) e)`). -/
theorem initBundleTree_origBucket (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) {e : ℕ}
    (he : e ∈ G.E) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    tr.origBucket e = bucketOf (tr.cs.lsf.wstr e * ℓ₀ e) := by
  intro tr
  show bucketOf (tr.cs.lsf.wstr e * safeLen G ℓ₀ e) = _
  rw [safeLen_eq_of_mem ℓ₀ he]

/-- **The clause of the edges in `AsmSdMapsAt`.** If the array at `bktH` holds the word of
`bucketOf (wstr e · ℓ₀ e)` at each edge `e` of `G` (as `bucketTable_runs` writes it), with the
stretch of the bundle state `tr` of the init, then it holds `bucketCode (tr.origBucket e)` at each
edge of `tr.cs.G₀ = G`. -/
theorem bucketTable_origBucket (lsfInit : LSFInit) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) (params : ℕ → SparsifyParams)
    (spanConst k M N : ℕ) (G : MGraph) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ)
    {mem : ℕ → ℕ} {bktH eCap : ℕ} (hElt : ∀ e ∈ G.E, e < eCap)
    (hW : ∀ e ∈ G.E, mem (bktH + e) = bucketCode (bucketOf
      ((initCompLSFWith lsfInit G ℓ₀ k j).lsf.wstr e * ℓ₀ e))) :
    let tr := initBundleTreeWithParams lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    ∀ e ∈ tr.cs.G₀.E, e < eCap ∧ mem (bktH + e) = bucketCode (tr.origBucket e) := by
  intro tr e he
  have he' : e ∈ G.E := he
  refine ⟨hElt e he', ?_⟩
  rw [hW e he', initBundleTree_origBucket lsfInit depth sparsify params spanConst k M N G ℓ₀ ord j
    he']
  rfl

end MinCostFlow.SparseCore.Program
