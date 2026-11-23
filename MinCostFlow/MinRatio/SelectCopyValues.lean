module

public import MinCostFlow.MinRatio.SelectBlocksParts
public import MinCostFlow.MinRatio.WireSelectHeapRebal
import WordRAM.Tactic

/-!
# Copying the values of listed edges (`SelectCopyValues`)

At an `Update`, the table of `g` on `G_0` in the select blocks changes only on the edges of the
batch: each inserted edge gets its gradient. The new values are already in memory, in a table of
the same layout (`Lk` limbs per edge name). This file copies the entries of the listed edges from
one table to the other, in `O(|list| · Lk)` steps. (The core lengths are not copied but computed,
in `SelectCoreLenFill.lean`.)

* `selCopyValuesBody copyTo` (`[src, dst, listPtr, len, Lk]`): for each edge `e` of the list at
  `listPtr`, copy the `Lk` limbs of entry `e` of the table at `src` to entry `e` of the table at
  `dst`, with `copyLimbsToBody` (procedure `copyTo`).
* `selCopyValues_meetsContract`: the listed entries are copied, every other word is kept. Cost
  `len · (18 Lk + 50) + 20`.
* `edgeValuesAt_of_copyValues`: the table at `dst` holds the new values on the new edge set.
* `selCopyValues_setG0`: with `dst = g0Ptr`, the call keeps every other part of the blocks and
  gives `g'` on the new `E0`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

/-- Copy the entries of the listed edges (`[src, dst, listPtr, len, Lk]`). -/
def selCopyValuesBody (copyTo : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 3)
    (.assign 6 (.load (.bin .add (.reg 2) (.reg 5))) ;;
     .call 7 copyTo [.bin .add (.reg 0) (.bin .mul (.reg 6) (.reg 4)),
       .bin .add (.reg 1) (.bin .mul (.reg 6) (.reg 4)), .reg 4]) ;;
  .ret (.const 0)

theorem selCopyValuesBody_noRand (copyTo : ℕ) : (selCopyValuesBody copyTo).NoRand := by
  simp [selCopyValuesBody, forRange, forUp, Stmt.NoRand]

/-- Generalized contract of `selCopyValuesBody` allowing a distinct source table capacity `srcCap`
(e.g., copying `G.m` initial edge gradients into an `eCap`-sized select block). -/
def selCopyValuesContractSrc (w srcCap eCap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ src dst listPtr Lk, args = [src, dst, listPtr, L.length, Lk] ∧
    16 < 2 ^ w ∧ src + srcCap * Lk < 2 ^ w ∧ dst + eCap * Lk < 2 ^ w ∧
    listPtr + L.length < 2 ^ w ∧
    (src + srcCap * Lk ≤ dst ∨ dst + eCap * Lk ≤ src) ∧
    (listPtr + L.length ≤ dst ∨ dst + eCap * Lk ≤ listPtr) ∧
    ListAt mem listPtr L ∧ (∀ e ∈ L, e < srcCap ∧ e < eCap) ∧
    (∀ e ∈ L, ∀ t < Lk, mem (src + e * Lk + t) < 2 ^ w)
  post args mem ret mem' := ∃ src dst listPtr Lk, args = [src, dst, listPtr, L.length, Lk] ∧
    ret = 0 ∧
    (∀ e ∈ L, ∀ t < Lk, mem' (dst + e * Lk + t) = mem (src + e * Lk + t)) ∧
    (∀ a, (a < dst ∨ dst + eCap * Lk ≤ a) → mem' a = mem a) ∧
    (∀ e < eCap, e ∉ L → ∀ t < Lk, mem' (dst + e * Lk + t) = mem (dst + e * Lk + t))
  cost args _ := L.length * (18 * args.getD 4 0 + 50) + 20

/-- Contract of `selCopyValuesBody` for the list `L` of edges below `eCap`. The two tables have
`eCap` entries of `Lk` words, they are disjoint, and the list lies off the destination. -/
def selCopyValuesContract (w eCap : ℕ) (L : List ℕ) : Contract where
  pre args mem := ∃ src dst listPtr Lk, args = [src, dst, listPtr, L.length, Lk] ∧
    16 < 2 ^ w ∧ src + eCap * Lk < 2 ^ w ∧ dst + eCap * Lk < 2 ^ w ∧
    listPtr + L.length < 2 ^ w ∧
    (src + eCap * Lk ≤ dst ∨ dst + eCap * Lk ≤ src) ∧
    (listPtr + L.length ≤ dst ∨ dst + eCap * Lk ≤ listPtr) ∧
    ListAt mem listPtr L ∧ (∀ e ∈ L, e < eCap) ∧
    (∀ e ∈ L, ∀ t < Lk, mem (src + e * Lk + t) < 2 ^ w)
  post args mem ret mem' := ∃ src dst listPtr Lk, args = [src, dst, listPtr, L.length, Lk] ∧
    ret = 0 ∧
    (∀ e ∈ L, ∀ t < Lk, mem' (dst + e * Lk + t) = mem (src + e * Lk + t)) ∧
    (∀ a, (a < dst ∨ dst + eCap * Lk ≤ a) → mem' a = mem a) ∧
    (∀ e < eCap, e ∉ L → ∀ t < Lk, mem' (dst + e * Lk + t) = mem (dst + e * Lk + t))
  cost args _ := L.length * (18 * args.getD 4 0 + 50) + 20

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num DynSpanner.Program

private theorem ent_lt {v c L i : ℕ} (hv : v < c) (hi : i < L) : v * L + i < c * L := by
  have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hv)
  rw [Nat.succ_mul] at this
  omega

/-- Two different entries of a table are disjoint. -/
private theorem ent_disj {e e' L t : ℕ} (hne : e ≠ e') (ht : t < L) :
    e * L + t < e' * L ∨ e' * L + L ≤ e * L + t := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · left
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega
  · right
    have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega

set_option maxHeartbeats 400000 in
/-- `selCopyValuesBody` meets `selCopyValuesContractSrc` for distinct `(srcCap, eCap)`. -/
theorem selCopyValues_meetsContract_src {w proc copyTo srcCap eCap : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selCopyValuesBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selCopyValuesContractSrc w srcCap eCap L) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨src, dst, listPtr, Lk, rfl, hw16, hsrcW, hdstW, hlistW, hdisj, hldisj, hlist, hcap,
    hvalW⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hentSrc : ∀ e ∈ L, e * Lk + Lk ≤ srcCap * Lk := fun e he => by
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt (hcap e he).1)
    rw [Nat.succ_mul] at this; exact this
  have hentEnd : ∀ e ∈ L, e * Lk + Lk ≤ eCap * Lk := fun e he => by
    have := Nat.mul_le_mul_right Lk (Nat.succ_le_of_lt (hcap e he).2)
    rw [Nat.succ_mul] at this; exact this
  have hloop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := .assign 6 (.load (.bin .add (.reg 2) (.reg 5))) ;;
      .call 7 copyTo [.bin .add (.reg 0) (.bin .mul (.reg 6) (.reg 4)),
        .bin .add (.reg 1) (.bin .mul (.reg 6) (.reg 4)), .reg 4])
    (P := fun st => st = startState [src, dst, listPtr, L.length, Lk] mem pos)
    (Inv := fun i st => st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = listPtr ∧
      st.regs 3 = L.length ∧ st.regs 4 = Lk ∧ st.regs 5 = i ∧
      (∀ i' < i, ∀ (hi' : i' < L.length), ∀ t < Lk,
        st.mem (dst + L[i'] * Lk + t) = mem (src + L[i'] * Lk + t)) ∧
      (∀ a, (∀ i' < i, ∀ (hi' : i' < L.length),
        a < dst + L[i'] * Lk ∨ dst + L[i'] * Lk + Lk ≤ a) → st.mem a = mem a))
    (18 * Lk + 40) 0 L.length (Nat.zero_le _) hw1 (fun _ => by omega)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [startState]⟩)
    (fun _ _ _ _ hi => hi.2.2.2.2.2.1)
    (fun _ st _ _ hi => by have h3 := hi.2.2.2.1; eval_expr)
    (fun i _ hi => by
      intro st ω' hst
      rcases hst with ⟨h0, h1, h2, h3, h4, h5, hdone, hout⟩
      have heL : L[i] ∈ L := List.getElem_mem hi
      have heS := hentSrc _ heL
      have he := hentEnd _ heL
      have hread : st.mem (listPtr + i) = L[i] := by
        rw [hout _ fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi'); rcases hldisj with h | h <;> omega]
        exact hlist i hi
      have hsrcKeep : ∀ t < Lk, st.mem (src + L[i] * Lk + t) = mem (src + L[i] * Lk + t) :=
        fun t ht => hout _ fun i' _ hi' => by
          have := hentEnd _ (List.getElem_mem hi')
          rcases hdisj with h | h <;> omega
      apply runs_start_le
      refine runs_seq_assign_le (v := L[i]) (by eval_expr) ?_
      refine runs_call_le hcopy (vs := [src + L[i] * Lk, dst + L[i] * Lk, Lk]) (by eval_expr)
        (by wram_words) ⟨src + L[i] * Lk, dst + L[i] * Lk, Lk, rfl, hw1, by omega, by omega,
          by rcases hdisj with h | h <;> [left; right] <;> omega,
          fun t ht => by rw [hsrcKeep t ht]; exact hvalW _ heL t ht⟩ ?_
      intro v mem' pos' hpost
      obtain ⟨_, hcp, hfr⟩ := hpost
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hcp hfr
      refine ⟨⟨⟨by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4, by simp, fun i' hi'' hi' t ht => ?_, fun a ha => ?_⟩,
        by simpa using h5⟩, ?_⟩
      · dsimp only
        by_cases hii : L[i'] = L[i]
        · rw [hii, hcp t ht, hsrcKeep t ht]
        · have hne : i' ≠ i := fun h => hii (by subst h; rfl)
          rw [hfr _ (by rcases ent_disj hii ht with h | h <;> [left; right] <;> omega)]
          exact hdone i' (by omega) hi' t ht
      · dsimp only
        rw [hfr _ (ha i (by omega) hi)]
        exact hout a fun i' hi'' hi' => ha i' (by omega) hi'
      · simp only [copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ,
          Expr.size_reg, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil]
        omega)
  apply runs_start_le
  unfold selCopyValuesBody
  refine runs_seq_triple_le hloop rfl ?_
  intro st1 ⟨_, _, _, _, _, _, hdone, hout⟩
  refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
  · refine ⟨src, dst, listPtr, Lk, rfl, rfl, fun e he t ht => ?_, fun a ha => ?_,
      fun e he hnot t ht => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact hdone i hi hi t ht
    · refine hout a fun i' _ hi' => ?_
      have := hentEnd _ (List.getElem_mem hi')
      omega
    · refine hout _ fun i' _ hi' => ?_
      have hne : e ≠ L[i'] := fun h => hnot (h ▸ List.getElem_mem hi')
      rcases ent_disj hne ht with h | h <;> [left; right] <;> omega
  · simp only [selCopyValuesContractSrc, List.getD_cons_zero, List.getD_cons_succ, Expr.size,
      Nat.sub_zero]
    nlinarith

/-- `selCopyValuesBody` meets `selCopyValuesContract`. -/
theorem selCopyValues_meetsContract {w proc copyTo eCap : ℕ} {L : List ℕ} {p : Program}
    (hp : p.procs[proc]? = some (selCopyValuesBody copyTo))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (selCopyValuesContract w eCap L) := by
  have h := selCopyValues_meetsContract_src (srcCap := eCap) (eCap := eCap) (L := L) hp hcopy
  intro args mem pos ω hwords hpre
  obtain ⟨src, dst, listPtr, Lk, rfl, hw16, hsrcW, hdstW, hlistW, hdisj, hldisj, hlist, hcap, hvalW⟩ := hpre
  exact h _ mem pos ω hwords
    ⟨src, dst, listPtr, Lk, rfl, hw16, hsrcW, hdstW, hlistW, hdisj, hldisj, hlist,
      fun e he => ⟨hcap e he, hcap e he⟩, hvalW⟩

/-- **The table after the copy.** If the source table holds `vsrc` on every listed edge, the
destination table holds `vold` on `Eold`, and the new edge set `Enew` lies in `Eold` and the
list, then after the copy the destination holds `vnew`, which is `vsrc` on the listed edges and
`vold` on the others. -/
theorem edgeValuesAt_of_copyValues {w eCap P : ℕ} {L : List ℕ} {args : List ℕ}
    {mem mem' : ℕ → ℕ} {ret : ℕ} {Esrc Eold Enew : Finset ℕ} {vsrc vold vnew : ℕ → ℝ}
    (hpost : (selCopyValuesContract w eCap L).post args mem ret mem')
    (hsrc : EdgeValuesAt mem (args.getD 0 0) 4 (args.getD 4 0) P Esrc vsrc)
    (hold : EdgeValuesAt mem (args.getD 1 0) 4 (args.getD 4 0) P Eold vold)
    (hcapOld : ∀ e ∈ Eold, e < eCap)
    (hLsrc : ∀ e ∈ L, e ∈ Esrc)
    (hnew : ∀ e ∈ Enew, e ∈ L ∨ e ∈ Eold)
    (hvL : ∀ e ∈ Enew, e ∈ L → vnew e = vsrc e)
    (hvO : ∀ e ∈ Enew, e ∉ L → vnew e = vold e) :
    EdgeValuesAt mem' (args.getD 1 0) 4 (args.getD 4 0) P Enew vnew := by
  obtain ⟨src, dst, listPtr, Lk, rfl, _, hcp, _, hkeep⟩ := hpost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hsrc hold ⊢
  intro e he
  by_cases heL : e ∈ L
  · have hs := hsrc e (hLsrc e heL)
    refine ⟨fun t ht => (hcp e heL t ht) ▸ hs.1 t ht, ?_⟩
    unfold Num.fixVal
    rw [Num.intVal_congr (hcp e heL), hvL e he heL]
    exact hs.2
  · have heO := (hnew e he).resolve_left heL
    have hs := hold e heO
    have hk := hkeep e (hcapOld e heO) heL
    refine ⟨fun t ht => (hk t ht) ▸ hs.1 t ht, ?_⟩
    unfold Num.fixVal
    rw [Num.intVal_congr hk, hvO e he heL]
    exact hs.2

/-- **The gradient on `G_0` after a copy.** A copy into `g0Ptr` keeps every other part of the
blocks, and gives `g'` on the new edges `E0'`, from a source table that holds `gsrc` on the
listed edges. -/
theorem selCopyValues_setG0 {w P pLast : ℕ} {B : SelectBlocksLoc} {L : List ℕ} {src listPtr : ℕ}
    {mem mem' : ℕ → ℕ} {ret : ℕ} {D : SelBlocksData} {Esrc E0' : Finset ℕ} {gsrc g' : ℕ → ℝ}
    (hpost : (selCopyValuesContract w B.eCap L).post [src, B.g0Ptr, listPtr, L.length, B.Lk] mem
      ret mem')
    (hblk : SelBlocksDataAt mem B P D pLast)
    (hsrc : EdgeValuesAt mem src 4 B.Lk P Esrc gsrc) (hLsrc : ∀ e ∈ L, e ∈ Esrc)
    (hLcap : ∀ e ∈ L, e < B.eCap)
    (hnew : ∀ e ∈ E0', e ∈ L ∨ e ∈ D.E0)
    (hvL : ∀ e ∈ E0', e ∈ L → g' e = gsrc e) (hvO : ∀ e ∈ E0', e ∉ L → g' e = D.g e) :
    SelBlocksDataAt mem' B P { D with E0 := E0', g := g' } pLast := by
  have hG0 := hblk.2.2.2.2.2
  have hfr := hpost
  obtain ⟨_, _, _, _, hargs, _, _, hout, _⟩ := hfr
  simp only [List.cons.injEq] at hargs
  obtain ⟨rfl, rfl, rfl, -, rfl, -⟩ := hargs
  refine hblk.setG0 (fun a ha => hout a ?_) ⟨fun e he => ?_, ?_⟩
  · unfold SelectBlocksLoc.regG0 SelectBlocksLoc.endAddr at ha; omega
  · rcases hnew e he with h | h
    · exact hLcap e h
    · exact hG0.1 e h
  · exact edgeValuesAt_of_copyValues hpost hsrc hG0.2 hG0.1 hLsrc hnew hvL hvO

end MinCostFlow.MinRatio
