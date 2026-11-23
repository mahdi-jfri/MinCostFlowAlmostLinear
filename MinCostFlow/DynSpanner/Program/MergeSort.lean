module

public import MinCostFlow.DynSpanner.Program.MergeSortMerge
public import MinCostFlow.DynSpanner.Program.SortOps
public import WordRAM.Contract
public import WordRAM.Logic

import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Log

/-!
# Deterministic Word-RAM merge sort (`MergeSort`)

Verifies `mergePair_meetsContract` (`sortIdxMergePair = 0`) and `mergeSort_meetsContract`
(`sortIdxMergeSort = 1`) for `sortProcs bSort`. Bottom-up iterative merge sort runs
deterministically in `O(n * (Nat.log 2 (n + 1) + 1) + 1)` time using `[scratch, scratch + n)` as
auxiliary buffer.
-/

namespace MinCostFlow.DynSpanner.Program

open WordRAM

public section

private def BlocksSorted (L : List ℕ) (width : ℕ) : Prop :=
  ∀ k, ((L.drop (k * width)).take width).Pairwise (· ≤ ·)

private lemma blocksSorted_one (L : List ℕ) : BlocksSorted L 1 := by
  intro k
  cases h : L.drop (k * 1) with
  | nil => simp
  | cons x xs => simp

private lemma blocksSorted_of_le_width {L : List ℕ} {width : ℕ} (_h : L.length ≤ width) :
    L.Pairwise (· ≤ ·) → False → False := fun _ f => f

private lemma pairwise_of_blocksSorted {L : List ℕ} {width : ℕ}
    (hBS : BlocksSorted L width) (h : L.length ≤ width) : L.Pairwise (· ≤ ·) := by
  have h0 := hBS 0
  simpa [List.take_of_length_le h] using h0

private lemma drop_take_eq_of_eq_range {L' L : List ℕ} (hlen : L'.length = L.length)
    (lo width : ℕ) (_hhi : lo + width ≤ L'.length ∨ True)
    (heq : ∀ i < lo + width, i < L'.length → L'[i]? = L[i]?) :
    (L'.drop lo).take width = (L.drop lo).take width := by
  refine List.ext_getElem (by simp only [List.length_take, List.length_drop, hlen])
    fun r hr₁ hr₂ => ?_
  have hrw : min width (L'.length - lo) = ((L'.drop lo).take width).length := by
    rw [List.length_take, List.length_drop]
  have hlt1 : r < width := (Nat.lt_min.mp (hrw ▸ hr₁)).1
  have hlt2 : lo + r < L'.length := by
    have := (Nat.lt_min.mp (hrw ▸ hr₁)).2
    omega
  rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
  have hq := heq (lo + r) (by omega) hlt2
  rw [List.getElem?_eq_getElem hlt2, List.getElem?_eq_getElem (hlen ▸ hlt2)] at hq
  exact Option.some.inj hq

private lemma drop_take_eq_of_eq_ge {L' L : List ℕ} (hlen : L'.length = L.length)
    (lo width : ℕ) (heq : ∀ i, lo ≤ i → L'[i]? = L[i]?) :
    (L'.drop lo).take width = (L.drop lo).take width := by
  refine List.ext_getElem (by simp only [List.length_take, List.length_drop, hlen])
    fun r hr₁ hr₂ => ?_
  have hlt : lo + r < L'.length := by
    simp only [List.length_take, List.length_drop] at hr₁
    omega
  rw [List.getElem_take, List.getElem_drop, List.getElem_take, List.getElem_drop]
  have hq := heq (lo + r) (Nat.le_add_right _ _)
  rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem (hlen ▸ hlt)] at hq
  exact Option.some.inj hq

private lemma pairwise_take {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} (n : ℕ), l.Pairwise R → (l.take n).Pairwise R
  | [], _, _ => by simp
  | _, 0, _ => by simp
  | x :: xs, n + 1, h => by
    simp only [List.take_succ_cons, List.pairwise_cons] at h ⊢
    exact ⟨fun y hy => h.1 y (List.mem_of_mem_take hy), pairwise_take n h.2⟩

private lemma pairwise_drop {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} (n : ℕ), l.Pairwise R → (l.drop n).Pairwise R
  | l, 0, h => by simpa using h
  | [], _ + 1, _ => by simp
  | _ :: xs, n + 1, h => by
    simp only [List.drop_succ_cons]
    exact pairwise_drop n (List.pairwise_cons.mp h).2

private lemma blocksSorted_of_pairwise {L : List ℕ} (hP : L.Pairwise (· ≤ ·)) (width : ℕ) :
    BlocksSorted L width := fun k => pairwise_take width (pairwise_drop (k * width) hP)

private lemma list_slice_split {α : Type*} (L : List α) {lo hi : ℕ}
    (hlo : lo ≤ hi) (_hhi : hi ≤ L.length) :
    L.take lo ++ (L.drop lo).take (hi - lo) ++ L.drop hi = L := by
  rw [List.append_assoc]
  have hsplit : (L.drop lo).take (hi - lo) ++ L.drop hi = L.drop lo := by
    conv_rhs => rw [← List.take_append_drop (hi - lo) (L.drop lo)]
    rw [List.drop_drop, show lo + (hi - lo) = hi by omega]
  rw [hsplit, List.take_append_drop]

private lemma list_eq_take_of_eq_lt {L' L : List ℕ} {lo : ℕ}
    (hlo : lo ≤ L.length) (hlen : L'.length = L.length)
    (heq : ∀ i < lo, L'[i]? = L[i]?) :
    L'.take lo = L.take lo := by
  refine List.ext_getElem (by simp only [List.length_take, hlen]) fun r hr₁ hr₂ => ?_
  have hr_lo : r < lo := by
    simp only [List.length_take] at hr₁; omega
  have hr_len : r < L'.length := by
    simp only [List.length_take] at hr₁; omega
  rw [List.getElem_take, List.getElem_take]
  have hq := heq r hr_lo
  rw [List.getElem?_eq_getElem hr_len, List.getElem?_eq_getElem (hlen ▸ hr_len)] at hq
  exact Option.some.inj hq

private lemma list_eq_drop_of_eq_ge {L' L : List ℕ} {hi : ℕ}
    (hlen : L'.length = L.length) (heq : ∀ i, hi ≤ i → L'[i]? = L[i]?) :
    L'.drop hi = L.drop hi := by
  refine List.ext_getElem (by simp only [List.length_drop, hlen]) fun r hr₁ hr₂ => ?_
  have hr_len : hi + r < L'.length := by
    simp only [List.length_drop] at hr₁; omega
  rw [List.getElem_drop, List.getElem_drop]
  have hq := heq (hi + r) (Nat.le_add_right _ _)
  rw [List.getElem?_eq_getElem hr_len, List.getElem?_eq_getElem (hlen ▸ hr_len)] at hq
  exact Option.some.inj hq

private lemma list_perm_of_slice {L' L : List ℕ} {lo hi : ℕ}
    (hlo : lo ≤ hi) (hhi : hi ≤ L.length) (hlen : L'.length = L.length)
    (hlt : ∀ i < lo, L'[i]? = L[i]?)
    (hge : ∀ i, hi ≤ i → L'[i]? = L[i]?)
    (hmid : ((L'.drop lo).take (hi - lo)).Perm ((L.drop lo).take (hi - lo))) :
    L'.Perm L := by
  have hrecon' := list_slice_split L' hlo (hlen.symm ▸ hhi)
  have hrecon := list_slice_split L hlo hhi
  rw [← hrecon', ← hrecon, list_eq_take_of_eq_lt (le_trans hlo hhi) hlen hlt,
    list_eq_drop_of_eq_ge hlen hge]
  exact ((List.Perm.refl _).append hmid).append (.refl _)

private lemma halveOuter_step {n w : ℕ} (_hw1 : 1 ≤ w) (hwn : w < n) :
    (if n ≤ 2 * w then 0 else Nat.log 2 ((n - 1) / (2 * w)) + 1) + 1 ≤
      Nat.log 2 ((n - 1) / w) + 1 := by
  split_ifs with h2
  · exact Nat.le_add_left _ _
  · have h2w_lt : 2 * w < n := Nat.lt_of_not_le h2
    have hq_pos : 1 ≤ (n - 1) / (2 * w) := Nat.div_pos (by omega) (by omega)
    have hpow : 2 ^ (Nat.log 2 ((n - 1) / (2 * w)) + 1) ≤ (n - 1) / w := by
      have hp := Nat.pow_log_le_self 2 (by omega : (n - 1) / (2 * w) ≠ 0)
      have hdiv2 : 2 * ((n - 1) / (2 * w)) ≤ (n - 1) / w := by
        rw [Nat.mul_comm 2 w, ← Nat.div_div_eq_div_mul]
        exact Nat.mul_div_le _ 2
      rw [Nat.pow_succ']
      omega
    exact Nat.succ_le_succ (Nat.le_log_of_pow_le (by omega) hpow)

theorem mergeSort_meetsContract {w : ℕ} {p : Program} {b bSort : ℕ} {L : List ℕ}
    (hp : p.HasAt b (sortProcs bSort)) (hpSort : p.HasAt bSort (sortProcs bSort)) :
    MeetsContract w p (b + sortIdxMergeSort) (mergeSortContract w L) := by
  refine meetsContract_of_runs (hp.get (i := sortIdxMergeSort) (by simp [sortProcs, sortIdxMergeSort]))
    fun args mem pos _ hargs hpre => ?_
  rcases hpre with ⟨a, scratch, rfl, hw16, haB, hscB, hdisj, hLat, hLw⟩
  let n := L.length
  have hlt_a : a < 2 ^ w := hargs a (by simp)
  have hlt_n : n < 2 ^ w := hargs n (by simp [n])
  have hlt_sc : scratch < 2 ^ w := hargs scratch (by simp)
  have h0_lt : (0 : ℕ) < 2 ^ w := by omega
  have h1_lt : (1 : ℕ) < 2 ^ w := by omega
  have h2_lt : (2 : ℕ) < 2 ^ w := by omega
  refine runs_start_le ?_
  dsimp only [sortProcs, sortIdxMergeSort, List.getElem_cons_succ, List.getElem_cons_zero,
    mergeSortStmt]
  refine runs_seq_assign_le (v := 1) (by eval_expr) ?_
  let halveO : ℕ → ℕ := fun width => if n ≤ width then 0 else Nat.log 2 ((n - 1) / width) + 1
  let InvO : State → Prop := fun st =>
    ∃ (width : ℕ) (cur : List ℕ),
      1 ≤ width ∧ (width < n ∨ width = n ∨ (n = 0 ∧ width = 1)) ∧
      cur.Perm L ∧ BlocksSorted cur width ∧
      st.regs 0 = a ∧ st.regs 1 = n ∧ st.regs 2 = scratch ∧ st.regs 3 = width ∧
      ListAt st.mem a cur ∧
      ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) → st.mem addr = mem addr
  let condO : Expr := .bin .lt (.reg 3) (.reg 1)
  let condI : Expr := .bin .lt (.reg 4) (.reg 1)
  let bodyI : Stmt :=
    .cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4)))
      (.assign 5 (.bin .add (.reg 4) (.reg 3)))
      (.assign 5 (.reg 1)) ;;
    .cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5)))
      (.assign 6 (.bin .add (.reg 5) (.reg 3)))
      (.assign 6 (.reg 1)) ;;
    .cond (.bin .lt (.reg 5) (.reg 6))
      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
      .nop ;;
    .assign 4 (.reg 6)
  let bodyO : Stmt :=
    .assign 4 (.const 0) ;;
    .loop condI bodyI ;;
    .cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 3)))
      (.assign 3 (.bin .mul (.const 2) (.reg 3)))
      (.assign 3 (.reg 1))
  let mO : State → ℕ := fun st => halveO (st.regs 3)
  let remO : State → ℕ := fun st => (165 * n + 35) * halveO (st.regs 3) + 10
  let condValO : State → ℕ := fun st => if st.regs 3 < n then 1 else 0
  have hLoopO : Triple w p InvO (.loop condO bodyO) (normalPost fun st =>
      ∃ cur : List ℕ,
        cur.Perm L ∧ cur.Pairwise (· ≤ ·) ∧ ListAt st.mem a cur ∧
        ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
          st.mem addr = mem addr) remO := by
    refine Triple.loop_measure (condVal := condValO) (m := mO) (rem := remO)
      (fun st hInv => by
        rcases hInv with ⟨width, _, hw1, hw_bd, _, _, _, hr1, _, hr3, _, _⟩
        have hw_ltw : width < 2 ^ w := by rcases hw_bd with h | h | ⟨_, h⟩ <;> omega
        dsimp only [condO, condValO]
        by_cases hlt : width < n <;> simp [Expr.eval, BinOp.eval, hr1, hr3, hlt, h0_lt, h1_lt])
      (fun st hInv hv => by
        rcases hInv with ⟨width, cur, _, hw_bd, hperm, hBS, _, _, _, hr3, hcat, hfr⟩
        dsimp only [condValO] at hv
        have hn_le : n ≤ width := by rw [hr3] at hv; by_contra hc; simp [show width < n by omega] at hv
        have hlen_le : cur.length ≤ width := by rw [hperm.length_eq]; exact hn_le
        refine ⟨⟨cur, hperm, pairwise_of_blocksSorted hBS hlen_le, hcat, hfr⟩,
          by dsimp only [condO, Expr.size, remO]; rw [hr3]; dsimp only [halveO]; simp [hn_le]⟩)
      (fun st hInv hv => by
        rcases hInv with ⟨width, cur0, hw1, hw_bd, hperm0, hBS0, hr0, hr1, hr2, hr3, hcat0, hfr0⟩
        dsimp only [condValO] at hv
        have hw_lt : width < n := by rw [hr3] at hv; by_contra hc; simp [hc] at hv
        have hw_ltw : width < 2 ^ w := by omega
        let InvI : State → Prop := fun stI =>
          ∃ (lo : ℕ) (cur : List ℕ),
            lo ≤ n ∧ (lo < n → ∃ q, lo = q * (2 * width)) ∧
            cur.Perm L ∧
            (∀ k, k * (2 * width) < lo → ((cur.drop (k * (2 * width))).take (2 * width)).Pairwise (· ≤ ·)) ∧
            (∀ m, lo + m * width < n → ((cur.drop (lo + m * width)).take width).Pairwise (· ≤ ·)) ∧
            stI.regs 0 = a ∧ stI.regs 1 = n ∧ stI.regs 2 = scratch ∧
            stI.regs 3 = width ∧ stI.regs 4 = lo ∧
            ListAt stI.mem a cur ∧
            ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
              stI.mem addr = mem addr
        let mI : State → ℕ := fun stI => n - stI.regs 4
        let remI : State → ℕ := fun stI => 165 * (n - stI.regs 4) + 10
        let condValI : State → ℕ := fun stI => if stI.regs 4 < n then 1 else 0
        have hLoopI : Triple w p InvI (.loop condI bodyI) (normalPost fun stI =>
            ∃ cur : List ℕ,
              cur.Perm L ∧ BlocksSorted cur (2 * width) ∧
              stI.regs 0 = a ∧ stI.regs 1 = n ∧ stI.regs 2 = scratch ∧ stI.regs 3 = width ∧
              ListAt stI.mem a cur ∧
              ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
                stI.mem addr = mem addr) remI := by
          refine Triple.loop_measure (condVal := condValI) (m := mI) (rem := remI)
            (fun stI hInvI => by
              rcases hInvI with ⟨lo, _, hlo, _, _, _, _, _, hr1I, _, _, hr4I, _, _⟩
              dsimp only [condI, condValI]
              by_cases hlt : lo < n <;> simp [Expr.eval, BinOp.eval, hr1I, hr4I, hlt, h0_lt, h1_lt])
            (fun stI hInvI hvI => by
              rcases hInvI with ⟨lo, cur, hlo, _, hpermI, hdone, _, hr0I, hr1I, hr2I, hr3I, hr4I, hcatI, hfrI⟩
              dsimp only [condValI] at hvI
              have hn_lo : n ≤ lo := by rw [hr4I] at hvI; by_contra hc; simp [show lo < n by omega] at hvI
              have hlo_eq : lo = n := by omega
              have hBS2 : BlocksSorted cur (2 * width) := by
                intro k
                by_cases hk : k * (2 * width) < n
                · exact hdone k (hlo_eq ▸ hk)
                · have hlen_cur : cur.length = n := hpermI.length_eq
                  rw [List.drop_of_length_le (by omega), List.take_nil]
                  exact List.Pairwise.nil
              refine ⟨⟨cur, hpermI, hBS2, hr0I, hr1I, hr2I, hr3I, hcatI, hfrI⟩,
                by dsimp only [condI, Expr.size, remI]; rw [hr4I, hlo_eq]; omega⟩)
            (fun stI hInvI hvI => by
              rcases hInvI with ⟨lo, cur, hlo_le, hq_div, hpermI, hdone, htail,
                hr0I, hr1I, hr2I, hr3I, hr4I, hcatI, hfrI⟩
              dsimp only [condValI] at hvI
              have hlo_lt : lo < n := by rw [hr4I] at hvI; by_contra hc; simp [hc] at hvI
              rcases hq_div hlo_lt with ⟨q, hlo_q⟩
              have hcur_len : cur.length = n := hpermI.length_eq
              have hcur_w : ∀ x ∈ cur, x < 2 ^ w := fun x hx => hLw x (hpermI.mem_iff.mp hx)
              let mid := if width < n - lo then lo + width else n
              let hi := if width < n - mid then mid + width else n
              have hlo_mid : lo ≤ mid := by dsimp only [mid]; split_ifs <;> omega
              have hlo_lt_mid : lo < mid := by dsimp only [mid]; split_ifs <;> omega
              have hmid_hi : mid ≤ hi := by dsimp only [mid, hi]; split_ifs <;> omega
              have hhi_n : hi ≤ n := by dsimp only [mid, hi] at *; split_ifs <;> omega
              have hmid_ltw : mid < 2 ^ w := by omega
              have hhi_ltw : hi < 2 ^ w := by omega
              have hd_pos : 1 ≤ hi - lo := by omega
              let bodyCost : ℕ := 70 * (hi - lo) + 85
              refine ⟨bodyCost, ?_⟩
              intro s ω' hs_eq
              subst s
              suffices hbody : ∃ o s' c, Runs w p ω' bodyI stI o s' c ∧
                  (match o with
                    | .returned u => normalPost (fun stI =>
                        ∃ cur : List ℕ, cur.Perm L ∧ BlocksSorted cur (2 * width) ∧
                          stI.regs 0 = a ∧ stI.regs 1 = n ∧ stI.regs 2 = scratch ∧ stI.regs 3 = width ∧
                          ListAt stI.mem a cur ∧
                          ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
                            stI.mem addr = mem addr) (.returned u) s' ∧
                        condI.size + bodyCost + 1 ≤ remI stI
                    | .normal => InvI s' ∧ mI s' < mI stI ∧ condI.size + bodyCost + remI s' + 1 ≤ remI stI) ∧
                  0 + c ≤ bodyCost by
                rcases hbody with ⟨o, s', c, hr, hq, hc⟩
                exact ⟨o, s', c, hr, hq, by simpa using hc⟩
              let stAfterAssigns : State → Prop := fun stA =>
                stA.mem = stI.mem ∧
                stA.regs 0 = a ∧ stA.regs 1 = n ∧ stA.regs 2 = scratch ∧
                stA.regs 3 = width ∧ stA.regs 4 = lo ∧ stA.regs 5 = mid ∧ stA.regs 6 = hi
              have h_pre_merge : ∃ st5 st6 c₅ c₆,
                  Runs w p ω'
                    (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4)))
                      (.assign 5 (.bin .add (.reg 4) (.reg 3))) (.assign 5 (.reg 1))) stI .normal st5 c₅ ∧
                  Runs w p ω'
                    (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5)))
                      (.assign 6 (.bin .add (.reg 5) (.reg 3))) (.assign 6 (.reg 1))) st5 .normal st6 c₆ ∧
                  stAfterAssigns st6 ∧ c₅ ≤ 10 ∧ c₆ ≤ 10 := by
                have hcond1 : ∃ st5 c₅,
                    Runs w p ω'
                      (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4)))
                        (.assign 5 (.bin .add (.reg 4) (.reg 3))) (.assign 5 (.reg 1)))
                      stI .normal st5 c₅ ∧
                    st5.mem = stI.mem ∧ st5.regs 0 = a ∧ st5.regs 1 = n ∧ st5.regs 2 = scratch ∧
                    st5.regs 3 = width ∧ st5.regs 4 = lo ∧ st5.regs 5 = mid ∧ c₅ ≤ 10 := by
                  have hsub1 : n - lo < 2 ^ w := by omega
                  by_cases h1c : width < n - lo
                  · have hmid_eq : mid = lo + width := by simp [mid, h1c]
                    let st5 : State := { mem := stI.mem, regs := Function.update stI.regs 5 mid, pos := stI.pos }
                    have he1 : (Expr.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4))).eval w stI = some 1 := by
                      simp [Expr.eval, BinOp.eval, hr1I, hr3I, hr4I, hsub1, h1c, h1_lt]
                    have he2 : (Expr.bin .add (.reg 4) (.reg 3)).eval w stI = some mid := by
                      simp [Expr.eval, BinOp.eval, hr3I, hr4I, hmid_eq, hmid_eq ▸ hmid_ltw]
                    refine ⟨st5, 5 + (3 + 1) + 1,
                      runs_cond_iff.mpr ⟨1, 3 + 1, he1, by simpa using runs_assign_iff.mpr ⟨mid, he2, rfl, rfl, rfl⟩, rfl⟩,
                      rfl, by simp [st5, hr0I], by simp [st5, hr1I], by simp [st5, hr2I],
                      by simp [st5, hr3I], by simp [st5, hr4I], by simp [st5], by omega⟩
                  · have hmid_eq : mid = n := by simp [mid, h1c]
                    let st5 : State := { mem := stI.mem, regs := Function.update stI.regs 5 mid, pos := stI.pos }
                    have he1 : (Expr.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 4))).eval w stI = some 0 := by
                      simp [Expr.eval, BinOp.eval, hr1I, hr3I, hr4I, hsub1, h1c, h0_lt]
                    have he2 : (.reg 1 : Expr).eval w stI = some mid := by
                      simp [Expr.eval, hr1I, hmid_eq]
                    refine ⟨st5, 5 + (1 + 1) + 1,
                      runs_cond_iff.mpr ⟨0, 1 + 1, he1, by simpa using runs_assign_iff.mpr ⟨mid, he2, rfl, rfl, rfl⟩, rfl⟩,
                      rfl, by simp [st5, hr0I], by simp [st5, hr1I], by simp [st5, hr2I],
                      by simp [st5, hr3I], by simp [st5, hr4I], by simp [st5], by omega⟩
                rcases hcond1 with ⟨st5, c₅, hr5_run, h5m, h50, h51, h52, h53, h54, h55, hc5⟩
                have hsub2 : n - mid < 2 ^ w := by omega
                have hcond2 : ∃ st6 c₆,
                    Runs w p ω'
                      (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5)))
                        (.assign 6 (.bin .add (.reg 5) (.reg 3))) (.assign 6 (.reg 1)))
                      st5 .normal st6 c₆ ∧
                    stAfterAssigns st6 ∧ c₆ ≤ 10 := by
                  by_cases h2c : width < n - mid
                  · have hhi_eq : hi = mid + width := by simp [hi, h2c]
                    let st6 : State := { mem := st5.mem, regs := Function.update st5.regs 6 hi, pos := st5.pos }
                    have he1 : (Expr.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5))).eval w st5 = some 1 := by
                      simp [Expr.eval, BinOp.eval, h51, h53, h55, hsub2, h2c, h1_lt]
                    have he2 : (Expr.bin .add (.reg 5) (.reg 3)).eval w st5 = some hi := by
                      simp [Expr.eval, BinOp.eval, h53, h55, hhi_eq, hhi_eq ▸ hhi_ltw]
                    refine ⟨st6, 5 + (3 + 1) + 1,
                      runs_cond_iff.mpr ⟨1, 3 + 1, he1, by simpa using runs_assign_iff.mpr ⟨hi, he2, rfl, rfl, rfl⟩, rfl⟩,
                      ⟨h5m, by simp [st6, h50], by simp [st6, h51], by simp [st6, h52],
                       by simp [st6, h53], by simp [st6, h54], by simp [st6, h55], by simp [st6]⟩,
                      by omega⟩
                  · have hhi_eq : hi = n := by simp [hi, h2c]
                    let st6 : State := { mem := st5.mem, regs := Function.update st5.regs 6 hi, pos := st5.pos }
                    have he1 : (Expr.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5))).eval w st5 = some 0 := by
                      simp [Expr.eval, BinOp.eval, h51, h53, h55, hsub2, h2c, h0_lt]
                    have he2 : (.reg 1 : Expr).eval w st5 = some hi := by
                      simp [Expr.eval, h51, hhi_eq]
                    refine ⟨st6, 5 + (1 + 1) + 1,
                      runs_cond_iff.mpr ⟨0, 1 + 1, he1, by simpa using runs_assign_iff.mpr ⟨hi, he2, rfl, rfl, rfl⟩, rfl⟩,
                      ⟨h5m, by simp [st6, h50], by simp [st6, h51], by simp [st6, h52],
                       by simp [st6, h53], by simp [st6, h54], by simp [st6, h55], by simp [st6]⟩,
                      by omega⟩
                rcases hcond2 with ⟨st6, c₆, hr6_run, h6A, hc6⟩
                exact ⟨st5, st6, c₅, c₆, hr5_run, hr6_run, h6A, hc5, hc6⟩
              rcases h_pre_merge with ⟨st5, stA, c₅, c₆, hr5_run, hr6_run,
                ⟨hAm, hA0, hA1, hA2, hA3, hA4, hA5, hA6⟩, hc₅, hc₆⟩
              have finish_bodyI : ∀ (stM : State) (cur' : List ℕ) (c₂ : ℕ),
                  Runs w p ω'
                    (.cond (.bin .lt (.reg 5) (.reg 6))
                      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
                      .nop) stA .normal stM c₂ →
                  c₂ ≤ 70 * (hi - lo) + 60 →
                  cur'.Perm cur →
                  (∀ k, k * (2 * width) < hi → ((cur'.drop (k * (2 * width))).take (2 * width)).Pairwise (· ≤ ·)) →
                  (∀ m, hi + m * width < n → ((cur'.drop (hi + m * width)).take width).Pairwise (· ≤ ·)) →
                  stM.regs 0 = a → stM.regs 1 = n → stM.regs 2 = scratch →
                  stM.regs 3 = width → stM.regs 6 = hi →
                  ListAt stM.mem a cur' →
                  (∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
                    stM.mem addr = mem addr) →
                  ∃ o s' c, Runs w p ω' bodyI stI o s' c ∧
                    (match o with
                      | .returned u => normalPost (fun stI =>
                          ∃ cur : List ℕ, cur.Perm L ∧ BlocksSorted cur (2 * width) ∧
                            stI.regs 0 = a ∧ stI.regs 1 = n ∧ stI.regs 2 = scratch ∧ stI.regs 3 = width ∧
                            ListAt stI.mem a cur ∧
                            ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
                              stI.mem addr = mem addr) (.returned u) s' ∧
                          condI.size + bodyCost + 1 ≤ remI stI
                      | .normal => InvI s' ∧ mI s' < mI stI ∧ condI.size + bodyCost + remI s' + 1 ≤ remI stI) ∧
                    0 + c ≤ bodyCost := by
                intro stM cur' c₂ hr₂ hc₂ hpc hdone' htail' hM0 hM1 hM2 hM3 hM6 hcatM hfrM
                have hq_next : hi < n → ∃ q', hi = q' * (2 * width) := by
                  intro hhn
                  dsimp only [mid, hi] at *
                  split_ifs at hhn ⊢ with hc1 hc2 <;>
                    exact ⟨q + 1, by rw [Nat.succ_mul, ← hlo_q]; omega⟩
                let stF : State := { mem := stM.mem, regs := Function.update stM.regs 4 hi, pos := stM.pos }
                have hr₃ : Runs w p ω' (.assign 4 (.reg 6)) stM .normal stF 2 :=
                  runs_assign_iff.mpr ⟨hi, by simp [Expr.eval, hM6], rfl, rfl, rfl⟩
                have hr₂₃ : Runs w p ω'
                    ((.cond (.bin .lt (.reg 5) (.reg 6))
                      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
                      .nop) ;; .assign 4 (.reg 6)) stA .normal stF (c₂ + 2 + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨stM, c₂, 2, hr₂, hr₃, rfl⟩)
                have hr_234 : Runs w p ω'
                    (.cond (.bin .lt (.reg 3) (.bin .sub (.reg 1) (.reg 5)))
                      (.assign 6 (.bin .add (.reg 5) (.reg 3))) (.assign 6 (.reg 1)) ;;
                     (.cond (.bin .lt (.reg 5) (.reg 6))
                      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
                      .nop ;; .assign 4 (.reg 6))) st5 .normal stF (c₆ + (c₂ + 2 + 1) + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨stA, c₆, c₂ + 2 + 1, hr6_run, hr₂₃, rfl⟩)
                have hrun_full : Runs w p ω' bodyI stI .normal stF (c₅ + (c₆ + (c₂ + 2 + 1) + 1) + 1) :=
                  runs_seq_iff.mpr (Or.inr ⟨st5, c₅, c₆ + (c₂ + 2 + 1) + 1, hr5_run, hr_234, rfl⟩)
                refine ⟨.normal, stF, _, hrun_full,
                  ⟨⟨hi, cur', hhi_n, hq_next, hpc.trans hpermI, hdone', htail',
                    by simp [stF, hM0], by simp [stF, hM1], by simp [stF, hM2], by simp [stF, hM3],
                    by simp [stF], hcatM, hfrM⟩,
                    (by dsimp only [mI, stF]; simp [hr4I]; omega),
                    (by dsimp only [condI, Expr.size, bodyCost, remI, stF]; simp [hr4I]; omega)⟩,
                  by dsimp only [bodyCost]; omega⟩
              by_cases hmid_lt_hi : mid < hi
              · have hmid_eq : mid = lo + width := by
                  dsimp only [mid, hi] at hmid_lt_hi ⊢
                  split_ifs at hmid_lt_hi ⊢ with hc1 <;> omega
                have hL1_sort : ((cur.drop lo).take (mid - lo)).Pairwise (· ≤ ·) := by
                  rw [show mid - lo = width by omega]
                  simpa using htail 0 (by omega)
                have hL2_sort : ((cur.drop mid).take (hi - mid)).Pairwise (· ≤ ·) := by
                  have hnext := htail 1 (by omega)
                  rw [show lo + 1 * width = mid by omega] at hnext
                  have hsub : ((cur.drop mid).take width).take (hi - mid) = (cur.drop mid).take (hi - mid) := by
                    rw [List.take_take]; congr 1; dsimp only [hi] at *; split_ifs at * <;> omega
                  rw [← hsub]
                  exact pairwise_take (hi - mid) hnext
                have hpre_mp : (mergePairContract w cur lo mid hi).pre [a, scratch, lo, mid, hi] stA.mem :=
                  ⟨a, scratch, rfl, hw16, by omega, by omega,
                    by rcases hdisj with hd | hd <;> [left; right] <;> omega,
                    hlo_mid, hmid_hi, by omega, hAm ▸ hcatI, hcur_w, hL1_sort, hL2_sort⟩
                have hev_mp : evalArgs w stA [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6] =
                    some [a, scratch, lo, mid, hi] := by
                  simp [evalArgs, Expr.eval, hA0, hA2, hA4, hA5, hA6]
                rcases runs_call_of_meetsContract (r := 7) (mergePair_meetsContract hpSort)
                  hev_mp (by
                    simp only [List.mem_cons, List.not_mem_nil, or_false]
                    rintro z (hz | hz | hz | hz | hz) <;> subst hz
                    · exact hlt_a
                    · exact hlt_sc
                    · omega
                    · exact hmid_ltw
                    · exact hhi_ltw)
                  hpre_mp ω' with ⟨stM, cC, retC, hrC, hpC, _, hregsC, hcostC⟩
                rcases hpC with ⟨_, _, cur', hEqC, _, hlenC, hltC, hgeC, hmidC, hcatC, hfrC⟩
                simp only [List.cons.injEq, and_true] at hEqC
                rcases hEqC with ⟨rfl, rfl, rfl, rfl, rfl⟩
                have hperm_cur' : cur'.Perm cur := by
                  refine list_perm_of_slice (le_trans hlo_mid hmid_hi) (by omega) hlenC hltC hgeC ?_
                  rw [hmidC]
                  have hcomb : (cur.drop lo).take (hi - lo) =
                      (cur.drop lo).take (mid - lo) ++ (cur.drop mid).take (hi - mid) := by
                    rw [show hi - lo = (mid - lo) + (hi - mid) by omega, List.take_add, List.drop_drop,
                      show lo + (mid - lo) = mid by omega]
                  rw [hcomb]
                  exact natMerge_perm _ _
                have hdone_cur' : ∀ k, k * (2 * width) < hi →
                    ((cur'.drop (k * (2 * width))).take (2 * width)).Pairwise (· ≤ ·) := by
                  intro k hk
                  rcases lt_trichotomy k q with hkq | rfl | hkq
                  · have hk_bound : (k + 1) * (2 * width) ≤ lo := by rw [hlo_q]; exact Nat.mul_le_mul_right _ hkq
                    have heq_sl := drop_take_eq_of_eq_range hlenC (k * (2 * width)) (2 * width) (Or.inr trivial)
                      fun idx hidx _ => hltC idx (by rw [← Nat.succ_mul] at hidx; exact lt_of_lt_of_le hidx hk_bound)
                    rw [heq_sl]
                    have hk_lo : k * (2 * width) < lo := by
                      have : k * (2 * width) < (k + 1) * (2 * width) := by
                        rw [Nat.add_mul, Nat.one_mul]
                        omega
                      exact lt_of_lt_of_le this hk_bound
                    exact hdone k hk_lo
                  · rw [← hlo_q]
                    have hhi_le_2w : hi - lo ≤ 2 * width := by
                      dsimp only [mid, hi] at *
                      split_ifs <;> omega
                    have hsub_take : (cur'.drop lo).take (2 * width) = (cur'.drop lo).take (hi - lo) := by
                      by_cases h2w : hi = lo + 2 * width
                      · rw [show hi - lo = 2 * width by omega]
                      · have hhi_n_eq : hi = n := by dsimp only [mid, hi] at *; split_ifs at * <;> omega
                        have hcur_len' : cur'.length = n := hlenC.trans hcur_len
                        rw [List.take_of_length_le (by simp [List.length_drop, hcur_len']; omega),
                            List.take_of_length_le (by simp [List.length_drop, hcur_len', hhi_n_eq])]
                    rw [hsub_take, hmidC]
                    exact natMerge_pairwise hL1_sort hL2_sort
                  · have hk_ge_hi : hi ≤ k * (2 * width) := by
                      have hhi_le : hi ≤ (q + 1) * (2 * width) := by
                        rw [Nat.succ_mul, ← hlo_q]
                        dsimp only [mid, hi] at *; split_ifs <;> omega
                      have hmono : (q + 1) * (2 * width) ≤ k * (2 * width) := Nat.mul_le_mul_right _ hkq
                      omega
                    omega
                have htail_cur' : ∀ m, hi + m * width < n →
                    ((cur'.drop (hi + m * width)).take width).Pairwise (· ≤ ·) := by
                  intro m hm
                  have hhi_lt_n : hi < n := by omega
                  have hhi_eq2 : hi = lo + 2 * width := by
                    dsimp only [mid, hi] at hhi_lt_n ⊢
                    split_ifs at hhi_lt_n ⊢ with hc1 hc2 <;> omega
                  have heq_sl := drop_take_eq_of_eq_ge hlenC (hi + m * width) width
                    fun idx hidx => hgeC idx (by omega)
                  rw [heq_sl]
                  have heq_idx : lo + (m + 2) * width = hi + m * width := by
                    rw [Nat.add_mul, Nat.add_comm (m * width) (2 * width), ← Nat.add_assoc, ← hhi_eq2]
                  have htailm := htail (m + 2) (by rw [heq_idx]; exact hm)
                  rwa [heq_idx] at htailm
                have he_cond3 : (Expr.bin .lt (.reg 5) (.reg 6)).eval w stA = some 1 := by
                  simp [Expr.eval, BinOp.eval, hA5, hA6, hmid_lt_hi, h1_lt]
                have hr_cond3 : Runs w p ω'
                    (.cond (.bin .lt (.reg 5) (.reg 6))
                      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
                      .nop) stA .normal stM (3 + cC + 1) :=
                  runs_cond_iff.mpr ⟨1, cC, he_cond3, by simpa using hrC, rfl⟩
                dsimp only [mergePairContract, argsSize, Expr.size] at hcostC
                refine finish_bodyI stM cur' (3 + cC + 1) hr_cond3 (by omega) hperm_cur' hdone_cur' htail_cur'
                  (by rw [hregsC 0 (by decide), hA0]) (by rw [hregsC 1 (by decide), hA1])
                  (by rw [hregsC 2 (by decide), hA2]) (by rw [hregsC 3 (by decide), hA3])
                  (by rw [hregsC 6 (by decide), hA6]) hcatC
                  (fun addr h1a h2a => by
                    rw [hfrC addr (by rcases h1a with h1a | h1a <;> [left; right] <;> omega)
                      (by rcases h2a with h2a | h2a <;> [left; right] <;> omega), hAm]
                    exact hfrI addr h1a h2a)
              · have hhi_eq_mid : hi = mid := by omega
                have hhi_eq_n : hi = n := by
                  dsimp only [mid, hi] at hmid_lt_hi hhi_eq_mid ⊢
                  split_ifs at hmid_lt_hi hhi_eq_mid ⊢ with hc1 hc2 <;> omega
                have hn_le_lo_w : n ≤ lo + width := by
                  dsimp only [mid, hi] at hmid_lt_hi ⊢
                  split_ifs at hmid_lt_hi ⊢ with hc1 hc2 <;> omega
                have hdone_cur : ∀ k, k * (2 * width) < hi →
                    ((cur.drop (k * (2 * width))).take (2 * width)).Pairwise (· ≤ ·) := by
                  intro k hk
                  by_cases hkl : k * (2 * width) < lo
                  · exact hdone k hkl
                  · have hkq : k = q := by
                      have h1 : k * (2 * width) < lo + 2 * width := by
                        rw [hhi_eq_n] at hk
                        omega
                      have h2 : k * (2 * width) < (q + 1) * (2 * width) := by
                        rw [Nat.add_mul, Nat.one_mul, ← hlo_q]
                        exact h1
                      have hkq1 : k < q + 1 := by
                        by_contra hge
                        have hle : (q + 1) * (2 * width) ≤ k * (2 * width) :=
                          Nat.mul_le_mul_right _ (Nat.le_of_not_lt hge)
                        exact absurd h2 (Nat.not_lt.mpr hle)
                      have hq_le_k : q ≤ k := by
                        by_contra hlt_k
                        have hlt : k * (2 * width) < lo :=
                          hlo_q ▸ Nat.mul_lt_mul_of_pos_right (Nat.lt_of_not_le hlt_k) (by omega)
                        exact hkl hlt
                      omega
                    rw [hkq, ← hlo_q]
                    have htake_eq : (cur.drop lo).take (2 * width) = (cur.drop lo).take width := by
                      rw [List.take_of_length_le (by simp [List.length_drop, hcur_len]; omega),
                          List.take_of_length_le (by simp [List.length_drop, hcur_len]; omega)]
                    rw [htake_eq]
                    simpa using htail 0 (by simpa using hlo_lt)
                have htail_cur : ∀ m, hi + m * width < n →
                    ((cur.drop (hi + m * width)).take width).Pairwise (· ≤ ·) := fun m hm => by omega
                have he_cond3 : (Expr.bin .lt (.reg 5) (.reg 6)).eval w stA = some 0 := by
                  simp [Expr.eval, BinOp.eval, hA5, hA6, hhi_eq_mid, h0_lt]
                have hr_cond3 : Runs w p ω'
                    (.cond (.bin .lt (.reg 5) (.reg 6))
                      (.call 7 (bSort + sortIdxMergePair) [.reg 0, .reg 2, .reg 4, .reg 5, .reg 6])
                      .nop) stA .normal stA (3 + 1 + 1) :=
                  runs_cond_iff.mpr ⟨0, 1, he_cond3, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩
                exact finish_bodyI stA cur (3 + 1 + 1) hr_cond3 (by omega) (List.Perm.refl _) hdone_cur
                  htail_cur hA0 hA1 hA2 hA3 hA6 (hAm ▸ hcatI) (fun addr h1a h2a => hAm ▸ hfrI addr h1a h2a))
        refine ⟨165 * n + 30, ?_⟩
        intro s ω' hs_eq
        subst s
        suffices hbodyO : ∃ o s' c, Runs w p ω' bodyO st o s' c ∧
            (match o with
              | .returned u => normalPost (fun st =>
                  ∃ cur : List ℕ, cur.Perm L ∧ cur.Pairwise (· ≤ ·) ∧ ListAt st.mem a cur ∧
                    ∀ addr, (addr < a ∨ a + n ≤ addr) → (addr < scratch ∨ scratch + n ≤ addr) →
                      st.mem addr = mem addr) (.returned u) s' ∧
                  condO.size + (165 * n + 30) + 1 ≤ remO st
              | .normal => InvO s' ∧ mO s' < mO st ∧ condO.size + (165 * n + 30) + remO s' + 1 ≤ remO st) ∧
            0 + c ≤ 165 * n + 30 by
          rcases hbodyO with ⟨o, s', c, hr, hq, hc⟩
          exact ⟨o, s', c, hr, hq, by simpa using hc⟩
        dsimp only [bodyO]
        refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
        refine runs_seq_triple_le hLoopI
          ⟨0, cur0, Nat.zero_le _, fun _ => ⟨0, (Nat.zero_mul _).symm⟩, hperm0,
            fun k hk => absurd hk (Nat.not_lt_zero _),
            fun m _ => by simpa [Nat.zero_add] using hBS0 m,
            hr0, hr1, hr2, hr3, rfl, hcat0, hfr0⟩ ?_
        intro stI ⟨curI, hpermI, hBS2, hr0I, hr1I, hr2I, hr3I, hcatI, hfrI⟩
        have hsub_w : n - width < 2 ^ w := by omega
        by_cases h2w : width < n - width
        · have h2w_lt_n : 2 * width < n := by omega
          have h2w_ltw : 2 * width < 2 ^ w := by omega
          refine runs_cond_le_ms (v := 1)
            (by simp [Expr.eval, BinOp.eval, hr1I, hr3I, hsub_w, h2w, h1_lt]) ?_ ?_
          · intro _
            refine runs_assign_le (v := 2 * width)
              (by simp [Expr.eval, BinOp.eval, h2_lt, hr3I, h2w_ltw]) ?_
              (by dsimp only [Expr.size, remI]; simp only [Function.update_self, Nat.sub_zero]; omega)
            refine ⟨⟨2 * width, curI, by omega, Or.inl h2w_lt_n, hpermI, hBS2,
              hr0I, hr1I, hr2I, by simp, hcatI, hfrI⟩, ?_, ?_⟩
            · dsimp only [mO, halveO]
              have hnw : ¬ n ≤ width := Nat.not_le_of_lt hw_lt
              simp only [Function.update_self, hr3, hnw, ↓reduceIte]
              exact Nat.lt_of_succ_le (halveOuter_step hw1 hw_lt)
            · dsimp only [condO, Expr.size, remO, halveO]
              have hnw : ¬ n ≤ width := Nat.not_le_of_lt hw_lt
              simp only [Function.update_self, hr3, hnw, ↓reduceIte]
              have hstep := halveOuter_step hw1 hw_lt
              have hle := Nat.mul_le_mul_left (165 * n + 35) hstep
              rw [Nat.mul_add, Nat.mul_one] at hle
              omega
          · intro hc; cases hc
        · have hn_le_2w : n ≤ 2 * width := by omega
          have hpairI : curI.Pairwise (· ≤ ·) :=
            pairwise_of_blocksSorted hBS2 (by rw [hpermI.length_eq]; exact hn_le_2w)
          refine runs_cond_le_ms (v := 0)
            (by simp [Expr.eval, BinOp.eval, hr1I, hr3I, hsub_w, h2w, h0_lt]) ?_ ?_
          · intro hc; exact absurd rfl hc
          · intro _
            refine runs_assign_le (v := n) (by simp [Expr.eval, hr1I]) ?_
              (by dsimp only [Expr.size, remI]; simp only [Function.update_self, Nat.sub_zero]; omega)
            refine ⟨⟨n, curI, by omega, Or.inr (Or.inl rfl), hpermI,
              blocksSorted_of_pairwise hpairI n,
              hr0I, hr1I, hr2I, by simp, hcatI, hfrI⟩, ?_, ?_⟩
            · dsimp only [mO, halveO]
              have hnw : ¬ n ≤ width := Nat.not_le_of_lt hw_lt
              simp only [Function.update_self, hr3, le_refl, ↓reduceIte, hnw]
              exact Nat.succ_pos _
            · dsimp only [condO, Expr.size, remO, halveO]
              have hnw : ¬ n ≤ width := Nat.not_le_of_lt hw_lt
              simp only [Function.update_self, hr3, le_refl, ↓reduceIte, hnw, Nat.mul_zero]
              have hpos : 165 * n + 35 ≤ (165 * n + 35) * (Nat.log 2 ((n - 1) / width) + 1) :=
                Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
              omega)
  refine runs_seq_triple_le hLoopO
    ⟨1, L, le_refl _,
      (by by_cases hn0 : n = 0
          · right; right; exact ⟨hn0, rfl⟩
          · by_cases hn1 : n = 1
            · right; left; exact hn1.symm
            · left; omega),
      List.Perm.refl _, blocksSorted_one L,
      by simp [startState], by simp [startState, n], by simp [startState], by simp [startState],
      hLat, fun _ _ _ => rfl⟩ ?_
  intro stO ⟨curO, hpermO, hpairO, hcatO, hfrO⟩
  refine runs_ret_le (by eval_expr) ⟨a, scratch, curO, rfl, rfl, hpermO, hpairO, hcatO, hfrO⟩ ?_
  dsimp only [mergeSortContract, remO, halveO, Expr.size]
  simp only [Function.update_self, Nat.div_one]
  by_cases hn1 : n ≤ 1
  · simp only [hn1, ↓reduceIte]
    omega
  · simp only [hn1, ↓reduceIte]
    have hfinal : (165 * n + 35) * (Nat.log 2 (n - 1) + 1) ≤ 200 * n * (Nat.log 2 (n + 1) + 1) := by
      have h1 : (165 * n + 35) * (Nat.log 2 (n - 1) + 1) ≤ (165 * n + 35) * (Nat.log 2 (n + 1) + 1) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log_mono_right (by omega)))
      have h2 : 165 * n + 35 ≤ 200 * n := by omega
      have h3 : (165 * n + 35) * (Nat.log 2 (n + 1) + 1) ≤ 200 * n * (Nat.log 2 (n + 1) + 1) :=
        Nat.mul_le_mul_right _ h2
      exact le_trans h1 h3
    dsimp only [n] at hfinal ⊢
    omega

end

end MinCostFlow.DynSpanner.Program
