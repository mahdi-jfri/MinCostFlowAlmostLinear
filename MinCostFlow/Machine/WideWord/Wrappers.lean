module

public import MinCostFlow.Machine.WideWord.Trie

/-!
# Memory wrappers for wide-word trie initialization and output readout

This file defines and verifies:
* `buildInitTrie`: writes `len` contiguous `L`-limb `h`-bit blocks from host memory into a fresh
  lazy trie representing `initMem x` in `O(L * len)` time using `≤ L + len * (L * 2^h + L)` bump words.
* `readOutLimbs`: reads keys `0, ..., len - 1` from a lazy trie into contiguous `L`-limb `h`-bit
  blocks in host memory in `O(L * len)` time.
-/

@[expose] public section

namespace MinCostFlow.WideWord

open WordRAM

/-! ### Module indices and procedures -/

def idxBuildInitTrie : ℕ := 0
def idxReadOutLimbs : ℕ := 1

/-- Builds a fresh trie representing `initMem x` from `len` contiguous `L`-limb blocks at `arrPtr`.
Args: `[rootPtr, hpPtr, arrPtr, len, L, h, 2 ^ h]`. Returns `0`. -/
def buildInitTrie (arithBase trieBase : ℕ) : Stmt :=
  .store (.reg 0) (.const 0) ;;
  .assign 7 (.load (.reg 1)) ;;
  .store (.reg 1) (.bin .add (.reg 7) (.reg 4)) ;;
  forRange 8 (.const 0) (.reg 3)
    (.call 9 (arithBase + idxFromHost) [.reg 8, .reg 7, .reg 4, .reg 6] ;;
     .call 9 (trieBase + idxTrieWrite)
       [.reg 0, .reg 1, .reg 7, .bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 4)), .reg 4, .reg 6]) ;;
  .ret (.const 0)

/-- Reads keys `0, ..., len - 1` from trie `root` into contiguous `L`-limb blocks at `outPtr`,
using `L`-word scratch buffer `keyPtr`. Args: `[root, keyPtr, outPtr, len, L, 2 ^ h]`. Returns `0`. -/
def readOutLimbs (arithBase trieBase : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 3)
    (.call 7 (arithBase + idxFromHost) [.reg 6, .reg 1, .reg 4, .reg 5] ;;
     .call 7 (trieBase + idxTrieRead)
       [.reg 0, .reg 1, .bin .add (.reg 2) (.bin .mul (.reg 6) (.reg 4)), .reg 4]) ;;
  .ret (.const 0)

def wrapperModule (arithBase trieBase : ℕ) : List Stmt :=
  [buildInitTrie arithBase trieBase, readOutLimbs arithBase trieBase]

theorem wrapperModule_length (arithBase trieBase : ℕ) :
    (wrapperModule arithBase trieBase).length = 2 := rfl

theorem buildInitTrie_noRand (arithBase trieBase : ℕ) : (buildInitTrie arithBase trieBase).NoRand := by
  simp [buildInitTrie, forRange, forUp, Stmt.NoRand]

theorem readOutLimbs_noRand (arithBase trieBase : ℕ) : (readOutLimbs arithBase trieBase).NoRand := by
  simp [readOutLimbs, forRange, forUp, Stmt.NoRand]

theorem wrapperModule_noRand (arithBase trieBase : ℕ) :
    ∀ s ∈ wrapperModule arithBase trieBase, s.NoRand := by
  intro s hs
  simp only [wrapperModule, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact buildInitTrie_noRand _ _
  · exact readOutLimbs_noRand _ _

/-! ### Contracts -/

def buildInitTrieContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ rootPtr hpPtr arrPtr len L h hp, ∃ x : List ℕ,
      args = [rootPtr, hpPtr, arrPtr, len, L, h, 2 ^ h] ∧
      1 ≤ L ∧ 1 ≤ h ∧ 2 * h + 2 ≤ w ∧ len = x.length ∧ len ≤ 2 ^ (L * h) ∧
      1 ≤ hp ∧ mem hpPtr = hp ∧ ZeroFrom mem hp ∧
      hp + L + len * (L * 2 ^ h + L) < 2 ^ w ∧
      rootPtr < hp ∧ hpPtr < hp ∧ rootPtr ≠ hpPtr ∧
      arrPtr + len * L ≤ hp ∧
      (∀ i < len * L, arrPtr + i ≠ rootPtr ∧ arrPtr + i ≠ hpPtr) ∧
      (∀ i (hi : i < x.length), LimbsAt mem (arrPtr + i * L) L h x[i])
  post args mem v mem' :=
    ∃ rootPtr hpPtr arrPtr len L h hp,
      args = [rootPtr, hpPtr, arrPtr, len, L, h, 2 ^ h] ∧ v = 0 ∧
      mem hpPtr = hp ∧
      mem hpPtr ≤ mem' hpPtr ∧ mem' hpPtr ≤ hp + L + len * (L * 2 ^ h + L) ∧
      (∀ (x : List ℕ), len = x.length →
        (∀ i (hi : i < x.length), LimbsAt mem (arrPtr + i * L) L h x[i]) →
        TrieRep mem' L h (mem' hpPtr) (mem' rootPtr) (initMem x)) ∧
      (∀ q, InTrie mem' L h L (mem' rootPtr) q → hp + L ≤ q ∧ q < mem' hpPtr) ∧
      ZeroFrom mem' (mem' hpPtr) ∧
      (∀ q, q ≠ rootPtr → q ≠ hpPtr → q < mem hpPtr → mem' q = mem q)
  cost args _ := match args with | [_, _, _, len, L, _, _] => (95 * L + 115) * len + 30 | _ => 0

def readOutLimbsContract (w : ℕ) : Contract where
  pre args mem :=
    ∃ root keyPtr outPtr len L h hp f,
      args = [root, keyPtr, outPtr, len, L, 2 ^ h] ∧
      1 ≤ L ∧ 1 ≤ h ∧ 2 * h + 2 ≤ w ∧ len ≤ 2 ^ (L * h) ∧
      hp < 2 ^ w ∧ keyPtr + L < 2 ^ w ∧ outPtr + len * L < 2 ^ w ∧
      (keyPtr + L ≤ outPtr ∨ outPtr + len * L ≤ keyPtr) ∧
      (∀ p, InTrie mem L h L root p → (p < keyPtr ∨ keyPtr + L ≤ p) ∧ (p < outPtr ∨ outPtr + len * L ≤ p)) ∧
      Subtrie mem L h hp L root f
  post args mem v mem' :=
    ∃ root keyPtr outPtr len L B,
      args = [root, keyPtr, outPtr, len, L, B] ∧ v = 0 ∧
      (∀ h hp f, B = 2 ^ h → Subtrie mem L h hp L root f →
        ∀ i < len, LimbsAt mem' (outPtr + i * L) L h (f i)) ∧
      (∀ p, (p < keyPtr ∨ keyPtr + L ≤ p) → (p < outPtr ∨ outPtr + len * L ≤ p) → mem' p = mem p)
  cost args _ := match args with | [_, _, _, len, L, _] => (70 * L + 80) * len + 20 | _ => 0

/-! ### Verification -/

private theorem mul_add_lt_mul {a b c d : ℕ} (ha : a < c) (hb : b < d) :
    a * d + b < c * d := by
  have h1 : a + 1 ≤ c := ha
  calc a * d + b < a * d + d := Nat.add_lt_add_left hb _
    _ = (a + 1) * d := by ring
    _ ≤ c * d := Nat.mul_le_mul_right d h1

theorem buildInitTrie_meetsContract {w : ℕ} {p : Program} {fProc arithBase trieBase : ℕ}
    (hFromHost : MeetsContract w p (arithBase + idxFromHost) (mwFromHostContract w))
    (hWrite : MeetsContract w p (trieBase + idxTrieWrite) (trieWriteContract w))
    (hProc : p.procs[fProc]? = some (buildInitTrie arithBase trieBase)) :
    MeetsContract w p fProc (buildInitTrieContract w) := by
  refine meetsContract_of_runs hProc ?_
  rintro args mem pos ω hwords ⟨rootPtr, hpPtr, arrPtr, len, L, h, hp, x, rfl,
    hL1, hh, hw2, hlen_eq, hlen_pow, hhp1, hmem_hp, hz0, hbound, hroot_lt, hhp_lt, hrhp_ne,
    harr_le, harr_disj, harr_limbs⟩
  subst hlen_eq
  have hB : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.one_le_pow h 2 (by norm_num)) hB
  have hlen_w : x.length < 2 ^ w := by
    have : x.length ≤ x.length * L := Nat.le_mul_of_pos_right _ hL1
    omega
  set keyPtr := hp
  set blockSz := L * 2 ^ h + L
  let prefFunc (i k : ℕ) : ℕ := if k < i then x.getD k 0 else 0
  have hloop : Triple w p
      (fun st => st.mem = Function.update (Function.update mem rootPtr 0) hpPtr (hp + L) ∧
        st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = arrPtr ∧
        st.regs 3 = x.length ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
        st.regs 7 = keyPtr)
      (forRange 8 (.const 0) (.reg 3)
        (.call 9 (arithBase + idxFromHost) [.reg 8, .reg 7, .reg 4, .reg 6] ;;
         .call 9 (trieBase + idxTrieWrite)
           [.reg 0, .reg 1, .reg 7, .bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 4)), .reg 4, .reg 6]))
      (normalPost fun st =>
        hp + L ≤ st.mem hpPtr ∧ st.mem hpPtr ≤ hp + L + x.length * blockSz ∧
        TrieRep st.mem L h (st.mem hpPtr) (st.mem rootPtr) (initMem x) ∧
        (∀ q, InTrie st.mem L h L (st.mem rootPtr) q → hp + L ≤ q ∧ q < st.mem hpPtr) ∧
        (∀ q, q ≠ rootPtr → q ≠ hpPtr → q < hp → st.mem q = mem q))
      (fun _ => (x.length - 0) * (90 * L + 90 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.strengthen_post (Triple.forRange_const (w := w) (p := p) (r := 8)
      (P := fun st => st.mem = Function.update (Function.update mem rootPtr 0) hpPtr (hp + L) ∧
        st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = arrPtr ∧
        st.regs 3 = x.length ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
        st.regs 7 = keyPtr)
      (lo := .const 0) (hi := .reg 3)
      (body :=
        .call 9 (arithBase + idxFromHost) [.reg 8, .reg 7, .reg 4, .reg 6] ;;
        .call 9 (trieBase + idxTrieWrite)
          [.reg 0, .reg 1, .reg 7, .bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 4)), .reg 4, .reg 6])
      (Inv := fun i st =>
        st.regs 0 = rootPtr ∧ st.regs 1 = hpPtr ∧ st.regs 2 = arrPtr ∧
        st.regs 3 = x.length ∧ st.regs 4 = L ∧ st.regs 5 = h ∧ st.regs 6 = 2 ^ h ∧
        st.regs 7 = keyPtr ∧ st.regs 8 = i ∧
        hp + L ≤ st.mem hpPtr ∧ st.mem hpPtr ≤ hp + L + i * blockSz ∧
        TrieRep st.mem L h (st.mem hpPtr) (st.mem rootPtr) (prefFunc i) ∧
        (∀ q, InTrie st.mem L h L (st.mem rootPtr) q → hp + L ≤ q ∧ q < st.mem hpPtr) ∧
        (∀ q, q ≠ rootPtr → q ≠ hpPtr → q < hp → st.mem q = mem q))
      (90 * L + 90) 0 x.length (Nat.zero_le _) hw1 (fun _ => hlen_w)
      (fun st ⟨hm, r0, r1, r2, r3, r4, r5, r6, r7⟩ => by
        have hmem_hp' : st.mem hpPtr = hp + L := by rw [hm, Function.update_self]
        have hmem_root' : st.mem rootPtr = 0 := by
          rw [hm, Function.update_of_ne hrhp_ne, Function.update_self]
        have hz_init : ZeroFrom st.mem (hp + L) := by
          rw [hm]
          exact ((hz0.mono (by omega : hp ≤ hp + L)).update_lt (by omega)).update_lt (by omega)
        have hsub_init : Subtrie st.mem L h (hp + L) L 0 (prefFunc 0) := by
          rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL1) with ⟨d', hd'⟩
          rw [hd']
          simp [Subtrie, prefFunc]
        refine ⟨by eval_expr, by simp [r0], by simp [r1], by simp [r2], by simp [r3],
          by simp [r4], by simp [r5], by simp [r6], by simp [r7], by simp,
          by rw [hmem_hp'], by rw [hmem_hp']; simp,
          ⟨by dsimp only; rw [hmem_hp']; exact Nat.le_trans hhp1 (Nat.le_add_right _ _),
            by rw [hmem_hp', hmem_root']; exact hsub_init, by rw [hmem_hp']; exact hz_init⟩,
          fun q hq => by rw [hmem_root'] at hq; exact False.elim (inTrie_zero_root _ _ _ _ _ hq),
          fun q hnq hnh hqp => by
            rw [hm, Function.update_of_ne hnh, Function.update_of_ne hnq]⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.2.2.1; eval_expr)
      (fun i _ hilt => by
        intro st _ ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8,
          hhp_ge, hhp_le, htrep, hfoot, hfr⟩
        set hp_i := st.mem hpPtr
        set root_i := st.mem rootPtr
        have hhp_i_1 : 1 ≤ hp_i := htrep.1
        have hhp_next_lt : hp_i + blockSz < 2 ^ w := by
          have h1 : (i + 1) * blockSz = i * blockSz + blockSz := by ring
          have hmul : (i + 1) * blockSz ≤ x.length * blockSz := Nat.mul_le_mul_right _ hilt
          dsimp only [blockSz] at *; omega
        have hkey_w : keyPtr + L < 2 ^ w := by omega
        have hi_w : i < 2 ^ w := lt_trans hilt hlen_w
        have hL_w : L < 2 ^ w := by omega
        refine runs_start_le ?_
        refine runs_seq_call_le hFromHost
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
          (by wram_words) ⟨i, keyPtr, L, h, rfl, hh, hw2, hkey_w⟩ ?_
        rintro _ mem₁ pos₁ ⟨v', k', L', h', heq_fh, _, hfh_limbs, hfr_fh⟩
        simp only [List.cons.injEq, and_true] at heq_fh
        rcases heq_fh with ⟨rfl, rfl, rfl, hp_eq⟩
        have hh_eq : h' = h := Nat.pow_right_injective (by norm_num) hp_eq.symm
        cases hh_eq
        have hi_lt_Lh : i < 2 ^ (L * h) := lt_of_lt_of_le hilt hlen_pow
        have hkey_limbs : LimbsAt mem₁ keyPtr L h i :=
          ⟨hi_lt_Lh, fun m hm => by
            have hmL : m < L := by simpa [toLimbs_length] using hm
            rw [hfh_limbs m hmL, toLimbs_getElem hmL]⟩
        have hmem₁_root : mem₁ rootPtr = root_i := hfr_fh rootPtr (by omega)
        have hmem₁_hp : mem₁ hpPtr = hp_i := hfr_fh hpPtr (by omega)
        have hsub₁ : Subtrie mem₁ L h hp_i L root_i (prefFunc i) := by
          refine subtrie_congr_mem (fun q hq => ?_) htrep.2.1
          rcases hfoot q hq with ⟨hq1, hq2⟩
          exact hfr_fh q (by omega)
        have hz₁ : ZeroFrom mem₁ hp_i := by
          intro q hq
          rw [hfr_fh q (by omega)]
          exact htrep.2.2 q hq
        have hfoot₁ : ∀ q, InTrie mem₁ L h L root_i q → hp + L ≤ q ∧ q < hp_i := by
          intro q hq
          rw [inTrie_congr_mem L root_i (fun p hp' => by
            rcases hfoot p hp' with ⟨hp1, hp2⟩; exact hfr_fh p (by omega)) q] at hq
          exact hfoot q hq
        have hnin_in : ∀ p, InTrie mem₁ L h L root_i p → hp + L ≤ p ∧ p < hp_i := hfoot₁
        have hm_arr_lt : arrPtr + i * L + L ≤ hp := by
          calc arrPtr + i * L + L = arrPtr + (i + 1) * L := by ring
            _ ≤ arrPtr + x.length * L := Nat.add_le_add_left (Nat.mul_le_mul_right L hilt) _
            _ ≤ hp := harr_le
        have hval_limbs : LimbsAt mem₁ (arrPtr + i * L) L h (x[i]) := by
          refine (harr_limbs i hilt).congr fun m hm1 hm2 => ?_
          rw [hfr_fh m (by omega)]
          have hm_off : m - arrPtr < x.length * L := by
            have : i * L + (L - 1) < x.length * L := mul_add_lt_mul hilt (by omega)
            omega
          have hne_rh := harr_disj (m - arrPtr) hm_off
          rw [show arrPtr + (m - arrPtr) = m by omega] at hne_rh
          exact hfr m hne_rh.1 hne_rh.2 (by omega)
        have hmul_w : i * L < 2 ^ w := by
          have : i * L ≤ x.length * L := Nat.mul_le_mul_right L (Nat.le_of_lt hilt)
          omega
        have haddr_val_w : arrPtr + i * L < 2 ^ w := by omega
        have hpre_wr : (trieWriteContract w).pre
            [rootPtr, hpPtr, keyPtr, arrPtr + i * L, L, 2 ^ h] mem₁ := by
          refine ⟨rootPtr, hpPtr, keyPtr, arrPtr + i * L, L, h, root_i, hp_i, prefFunc i, i, x[i],
            rfl, hL1, hh, hw2, hhp_i_1, hmem₁_root, hmem₁_hp, hsub₁, hz₁,
            by dsimp only [blockSz] at hhp_next_lt; omega,
            by omega, by omega, hrhp_ne,
            fun hin => by have := hnin_in rootPtr hin; omega,
            fun hin => by have := hnin_in hpPtr hin; omega,
            by omega, by omega,
            fun m hm => ⟨by omega, by omega, fun hin => by have := hnin_in (keyPtr + m) hin; omega⟩,
            fun m hm => ?_, hkey_limbs, hval_limbs⟩
          have hm_off : i * L + m < x.length * L := mul_add_lt_mul hilt hm
          have hdis := harr_disj (i * L + m) hm_off
          rw [← Nat.add_assoc] at hdis
          refine ⟨hdis.1, hdis.2, fun hin => by
            have := hnin_in (arrPtr + i * L + m) hin
            omega⟩
        refine runs_call_le hWrite
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (Expr.eval_add (by eval_expr) (Expr.eval_mul (by eval_expr) (by eval_expr) hmul_w) haddr_val_w)
              (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))))
          (by wram_words) hpre_wr (fun _ mem₂ pos₂ ⟨rp', hp', kp', vp', L', B', heq_wr, _, hpi_le, hpi_ub,
            hsub_upd, hz₂, hfr_wr⟩ => by
          simp only [List.cons.injEq, and_true] at heq_wr
          rcases heq_wr with ⟨rfl, rfl, rfl, rfl, rfl, hB_wr⟩
          dsimp only at hpi_le hpi_ub hsub_upd hz₂ hfr_wr
          have hmem₁_hp' : mem₁ hpPtr = hp_i := hmem₁_hp
          rw [hmem₁_hp'] at hpi_le hpi_ub
          rw [hmem₁_hp', hmem₁_root] at hsub_upd hfr_wr
          rw [← hB_wr] at hpi_ub
          obtain ⟨hsub₂, hfoot₂⟩ := hsub_upd h (prefFunc i) i (x[i]) hB_wr.symm
            hsub₁ hkey_limbs hval_limbs
          have hupd_pref : ∀ q, Function.update (prefFunc i) i (x[i]) q = prefFunc (i + 1) q := by
            intro q
            dsimp only [prefFunc, Function.update, List.getD_eq_getElem?_getD]
            by_cases hqi : q = i
            · subst hqi; simp [hilt]
            · simp only [hqi]
              by_cases hlt_i : q < i
              · have hlt_i1 : q < i + 1 := by omega
                simp [hlt_i, hlt_i1]
              · have hnot_i1 : ¬ q < i + 1 := by omega
                simp [hlt_i, hnot_i1]
          have hsub₂' : Subtrie mem₂ L h (mem₂ hpPtr) L (mem₂ rootPtr) (prefFunc (i + 1)) :=
            subtrie_congr_func (fun q _ => hupd_pref q) hsub₂
          refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
            by simp [r5], by simp [r6], by simp [r7], by simp,
            le_trans hhp_ge hpi_le,
            by dsimp only [blockSz] at hhp_le hpi_ub ⊢; rw [show (i + 1) * (L * 2 ^ h + L) = i * (L * 2 ^ h + L) + (L * 2 ^ h + L) by ring]; omega,
            ⟨le_trans htrep.1 hpi_le, hsub₂', hz₂⟩,
            fun q hq => by
              rcases hfoot₂ q hq with hq_old | hq_new
              · rcases hnin_in q hq_old with ⟨hq1, hq2⟩
                exact ⟨hq1, lt_of_lt_of_le hq2 hpi_le⟩
              · exact ⟨le_trans hhp_ge hq_new.1, hq_new.2⟩,
            fun q hnq hnh hqp => by
              have hnin_q : ¬ InTrie mem₁ L h L root_i q := fun hin => by
                have := hnin_in q hin; omega
              dsimp only
              rw [hfr_wr h q hB_wr.symm hnq hnh hnin_q (by omega), hfr_fh q (by omega), hfr q hnq hnh hqp]⟩, r8⟩,
            by dsimp only [mwFromHostContract, trieWriteContract]; wram_cost⟩)))
      (fun o st hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨_, _, _, _, _, _, _, _, _, hhp_ge, hhp_le, htrep, hfoot, hfr⟩
          have hpref_eq : ∀ q < 2 ^ (L * h), prefFunc x.length q = initMem x q := by
            intro q _
            dsimp only [prefFunc, initMem, List.getD_eq_getElem?_getD]
            split_ifs with hq
            · simp [hq]
            · simp [List.getElem?_eq_none (Nat.le_of_not_lt hq)]
          have hsub_initMem : Subtrie st.mem L h (st.mem hpPtr) L (st.mem rootPtr) (initMem x) :=
            subtrie_congr_func hpref_eq htrep.2.1
          exact ⟨hhp_ge, hhp_le, ⟨htrep.1, hsub_initMem, htrep.2.2⟩, hfoot, hfr⟩)
  refine runs_start_le ?_
  dsimp only [buildInitTrie]
  refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
  refine runs_seq_assign_le (v := keyPtr)
    (Expr.eval_load_of_eq (by eval_expr)
      (by dsimp only [startState]; rw [Function.update_of_ne hrhp_ne.symm, hmem_hp])) ?_
  refine runs_seq_store_le (by eval_expr)
    (Expr.eval_add (by eval_expr) (by eval_expr) (by omega)) ?_
  refine runs_seq_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState],
    by simp [startState], by simp [startState]⟩ ?_
  rintro st_end ⟨hhp_ge, hhp_le, htrep, hfoot, hfr⟩
  refine runs_ret_le (by eval_expr)
    ⟨rootPtr, hpPtr, arrPtr, x.length, L, h, hp, rfl, rfl, hmem_hp,
      by rw [hmem_hp]; exact le_trans (by omega) hhp_ge,
      hhp_le,
      fun x' hx' hlim' => by
        have hlen_x' : x'.length = x.length := hx'.symm
        have hx_eq : x' = x := List.ext_getElem hlen_x' fun i hi1 hi2 => by
          exact (hlim' i hi1).ext (harr_limbs i hi2)
        subst hx_eq
        exact htrep,
      hfoot, htrep.2.2,
      fun q hnq hnh hqp => by rw [hmem_hp] at hqp; exact hfr q hnq hnh hqp⟩ ?_
  dsimp only [buildInitTrieContract]
  have hL_le : 90 * L + 90 + 1 + 8 ≤ 95 * L + 115 := by omega
  have hmul_le : x.length * (90 * L + 90 + 1 + 8) ≤ (95 * L + 115) * x.length := by
    rw [Nat.mul_comm x.length (90 * L + 90 + 1 + 8)]
    exact Nat.mul_le_mul_right _ hL_le
  simp only [Nat.sub_zero]
  wram_cost

theorem readOutLimbs_meetsContract {w : ℕ} {p : Program} {fProc arithBase trieBase : ℕ}
    (hFromHost : MeetsContract w p (arithBase + idxFromHost) (mwFromHostContract w))
    (hRead : MeetsContract w p (trieBase + idxTrieRead) (trieReadContract w))
    (hProc : p.procs[fProc]? = some (readOutLimbs arithBase trieBase)) :
    MeetsContract w p fProc (readOutLimbsContract w) := by
  refine meetsContract_of_runs hProc ?_
  rintro args mem pos ω hwords ⟨root, keyPtr, outPtr, len, L, h, hp, f, rfl,
    hL1, hh, hw2, hlen_pow, hhp_w, hkey_w, hout_w, hko_disj, hdisj, hsub⟩
  have hB : 2 ^ h < 2 ^ w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hw1 : 1 < 2 ^ w := lt_of_le_of_lt (Nat.one_le_pow h 2 (by norm_num)) hB
  have hroot_w : root < 2 ^ w := subtrie_root_lt hsub hhp_w hw1
  have hlen_w : len < 2 ^ w := by
    have : len ≤ len * L := Nat.le_mul_of_pos_right _ hL1
    omega
  have hL_w : L < 2 ^ w := hwords L (by simp)
  have hloop : Triple w p
      (fun st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = keyPtr ∧ st.regs 2 = outPtr ∧
        st.regs 3 = len ∧ st.regs 4 = L ∧ st.regs 5 = 2 ^ h)
      (forRange 6 (.const 0) (.reg 3)
        (.call 7 (arithBase + idxFromHost) [.reg 6, .reg 1, .reg 4, .reg 5] ;;
         .call 7 (trieBase + idxTrieRead)
           [.reg 0, .reg 1, .bin .add (.reg 2) (.bin .mul (.reg 6) (.reg 4)), .reg 4]))
      (normalPost fun st =>
        (∀ m < len, ∀ h' hp' f', 2 ^ h = 2 ^ h' → Subtrie mem L h' hp' L root f' →
          LimbsAt st.mem (outPtr + m * L) L h' (f' m)) ∧
        (∀ q, (q < keyPtr ∨ keyPtr + L ≤ q) → (q < outPtr ∨ outPtr + len * L ≤ q) →
          st.mem q = mem q))
      (fun _ => (len - 0) * (70 * L + 70 + (Expr.reg 3).size + 8) +
        ((Expr.const 0).size + (Expr.reg 3).size + 5)) := by
    refine Triple.strengthen_post (Triple.forRange_const (w := w) (p := p) (r := 6)
      (P := fun st => st.mem = mem ∧ st.regs 0 = root ∧ st.regs 1 = keyPtr ∧
        st.regs 2 = outPtr ∧ st.regs 3 = len ∧ st.regs 4 = L ∧ st.regs 5 = 2 ^ h)
      (lo := .const 0) (hi := .reg 3)
      (body :=
        .call 7 (arithBase + idxFromHost) [.reg 6, .reg 1, .reg 4, .reg 5] ;;
        .call 7 (trieBase + idxTrieRead)
          [.reg 0, .reg 1, .bin .add (.reg 2) (.bin .mul (.reg 6) (.reg 4)), .reg 4])
      (Inv := fun i st =>
        st.regs 0 = root ∧ st.regs 1 = keyPtr ∧ st.regs 2 = outPtr ∧
        st.regs 3 = len ∧ st.regs 4 = L ∧ st.regs 5 = 2 ^ h ∧ st.regs 6 = i ∧
        (∀ m < i, ∀ h' hp' f', 2 ^ h = 2 ^ h' → Subtrie mem L h' hp' L root f' →
          LimbsAt st.mem (outPtr + m * L) L h' (f' m)) ∧
        (∀ q, (q < keyPtr ∨ keyPtr + L ≤ q) → (q < outPtr ∨ outPtr + len * L ≤ q) →
          st.mem q = mem q))
      (70 * L + 70) 0 len (Nat.zero_le len) hw1 (fun _ => hlen_w)
      (fun st ⟨hm, r0, r1, r2, r3, r4, r5⟩ => by
        refine ⟨by eval_expr, by simp [r0], by simp [r1], by simp [r2], by simp [r3],
          by simp [r4], by simp [r5], by simp, fun m hm => absurd hm (Nat.not_lt_zero _),
          fun q _ _ => by rw [hm]⟩)
      (fun _ st _ _ hi => hi.2.2.2.2.2.2.1)
      (fun _ st _ _ hi => by have h3 := hi.2.2.2.1; eval_expr)
      (fun i _ hi_len => by
        intro st _ ⟨r0, r1, r2, r3, r4, r5, r6, hres, hfr⟩
        have hi_w : i < 2 ^ w := lt_trans hi_len hlen_w
        have hmul_w : i * L < 2 ^ w := by
          have : i * L ≤ len * L := Nat.mul_le_mul_right L (Nat.le_of_lt hi_len)
          omega
        have hdst_end_w : outPtr + i * L + L < 2 ^ w := by
          have : (i + 1) * L ≤ len * L := Nat.mul_le_mul_right L hi_len
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        have hdst_w : outPtr + i * L < 2 ^ w := by omega
        refine runs_start_le ?_
        refine runs_seq_call_le hFromHost
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
          (by wram_words) ⟨i, keyPtr, L, h, rfl, hh, hw2, hkey_w⟩ ?_
        rintro _ mem₁ pos₁ ⟨v', k', L', h', heq_fh, _, hfh_limbs, hfr_fh⟩
        simp only [List.cons.injEq, and_true] at heq_fh
        rcases heq_fh with ⟨rfl, rfl, rfl, hp_eq⟩
        have hh_eq : h' = h := Nat.pow_right_injective (by norm_num) hp_eq.symm
        cases hh_eq
        have hi_lt_Lh : i < 2 ^ (L * h) := lt_of_lt_of_le hi_len hlen_pow
        have hkey_limbs : LimbsAt mem₁ keyPtr L h i :=
          limbsAt_iff_pointwise.mpr ⟨hi_lt_Lh, fun m hm => hfh_limbs m hm⟩
        have hsub_cong : ∀ (hp' : ℕ) (f' : ℕ → ℕ),
            Subtrie mem L h hp' L root f' → Subtrie mem₁ L h hp' L root f' := by
          intro hp' f' hsub'
          refine subtrie_congr_mem (fun q hq => ?_) hsub'
          exact (hfr_fh q (hdisj q hq).1).trans (hfr q (hdisj q hq).1 (hdisj q hq).2)
        have hsub₁ : Subtrie mem₁ L h hp L root f := hsub_cong hp f hsub
        have hdisj₁ : ∀ q, InTrie mem₁ L h L root q →
            q < outPtr + i * L ∨ outPtr + i * L + L ≤ q := by
          intro q hq
          rw [inTrie_congr_mem L root (fun p hp' =>
            (hfr_fh p (hdisj p hp').1).trans (hfr p (hdisj p hp').1 (hdisj p hp').2)) q] at hq
          rcases (hdisj q hq).2 with hlt | hge
          · exact Or.inl (by omega)
          · have : (i + 1) * L ≤ len * L := Nat.mul_le_mul_right L hi_len
            rw [Nat.add_mul, Nat.one_mul] at this
            exact Or.inr (by omega)
        refine runs_call_le hRead
          (evalArgs_cons (by eval_expr) (evalArgs_cons (by eval_expr)
            (evalArgs_cons (Expr.eval_add (by eval_expr)
              (Expr.eval_mul (by eval_expr) (by eval_expr) hmul_w) hdst_w)
              (evalArgs_cons (by eval_expr) (evalArgs_nil _ _)))))
          (by wram_words) ⟨root, keyPtr, outPtr + i * L, L, h, hp, f, i,
            rfl, hh, hw2, hhp_w, hkey_w, hdst_end_w, hdisj₁, hsub₁, hkey_limbs⟩
          (fun _ mem₂ pos₂ ⟨root', kp', dst', L', heq_tr, _, htr_post, hfr_tr⟩ => by
          simp only [List.cons.injEq, and_true] at heq_tr
          rcases heq_tr with ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4],
            by simp [r5], by simp, fun m hm h' hp' f' hB_eq hsub' => ?_, fun q hqk hqo => ?_⟩, r6⟩,
            by dsimp only [mwFromHostContract, trieReadContract]; wram_cost⟩
          · by_cases hmi : m = i
            · subst m
              have hh' : h = h' := Nat.pow_right_injective (by norm_num) hB_eq
              subst hh'
              exact htr_post h hp' f' i (hsub_cong hp' f' hsub') hkey_limbs
            · have hm_lt : m < i := by omega
              have hold := hres m hm_lt h' hp' f' hB_eq hsub'
              refine hold.congr fun q hq1 hq2 => ?_
              have hq_end : (m + 1) * L ≤ i * L := Nat.mul_le_mul_right L hm_lt
              rw [Nat.add_mul, Nat.one_mul] at hq_end
              have hi_len_L : i * L ≤ len * L := Nat.mul_le_mul_right L (Nat.le_of_lt hi_len)
              have hq_out : q < outPtr + i * L := by omega
              have hq_key : q < keyPtr ∨ keyPtr + L ≤ q := by
                rcases hko_disj with hk | hk
                · exact Or.inr (by omega)
                · exact Or.inl (by omega)
              dsimp only
              rw [hfr_tr q (Or.inl hq_out)]
              dsimp only
              rw [hfr_fh q hq_key]
          · have hq_cur : q < outPtr + i * L ∨ outPtr + i * L + L ≤ q := by
              rcases hqo with h1 | h2
              · exact Or.inl (by omega)
              · have : (i + 1) * L ≤ len * L := Nat.mul_le_mul_right L hi_len
                rw [Nat.add_mul, Nat.one_mul] at this
                exact Or.inr (by omega)
            dsimp only
            rw [hfr_tr q hq_cur]
            dsimp only
            rw [hfr_fh q hqk, hfr q hqk hqo])))
      (fun o st hq => by
        cases o with
        | returned u => exact False.elim hq
        | normal =>
          rcases hq with ⟨_, _, _, _, _, _, _, hres, hfr⟩
          exact ⟨hres, hfr⟩)
  refine runs_start_le ?_
  dsimp only [readOutLimbs]
  refine runs_seq_triple_le hloop ⟨rfl, by simp [startState], by simp [startState],
    by simp [startState], by simp [startState], by simp [startState], by simp [startState]⟩ ?_
  rintro st_end ⟨hres_end, hfr_end⟩
  refine runs_ret_le (by eval_expr)
    ⟨root, keyPtr, outPtr, len, L, 2 ^ h, rfl, rfl,
      fun h' hp' f' hB_eq hsub' i hi => hres_end i hi h' hp' f' hB_eq hsub',
      hfr_end⟩ ?_
  dsimp only [readOutLimbsContract]
  have hL_le : 70 * L + 70 + 1 + 8 ≤ 70 * L + 80 := by omega
  have hmul_le : len * (70 * L + 70 + 1 + 8) ≤ (70 * L + 80) * len := by
    rw [Nat.mul_comm len (70 * L + 70 + 1 + 8)]
    exact Nat.mul_le_mul_right _ hL_le
  simp only [Nat.sub_zero]
  wram_cost

/-! ### Module wrappers -/

theorem wrapperModule_procs_at {p : Program} {b arithBase trieBase k : ℕ}
    (hp : p.HasAt b (wrapperModule arithBase trieBase))
    (hk : k < (wrapperModule arithBase trieBase).length) :
    p.procs[b + k]? = some (wrapperModule arithBase trieBase)[k] :=
  hp k hk

theorem buildInitTrie_of_module {w : ℕ} {p : Program} {b arithBase trieBase : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt trieBase (trieModule arithBase))
    (hWrap : p.HasAt b (wrapperModule arithBase trieBase)) :
    MeetsContract w p (b + idxBuildInitTrie) (buildInitTrieContract w) := by
  refine buildInitTrie_meetsContract (mwFromHost_of_arithModule hArith)
    (trieWrite_of_trieModule hArith hTrie) ?_
  have h := wrapperModule_procs_at hWrap (k := idxBuildInitTrie) (by rw [wrapperModule_length]; decide)
  simpa [wrapperModule, idxBuildInitTrie] using h

theorem readOutLimbs_of_module {w : ℕ} {p : Program} {b arithBase trieBase : ℕ}
    (hArith : p.HasAt arithBase (arithModule arithBase))
    (hTrie : p.HasAt trieBase (trieModule arithBase))
    (hWrap : p.HasAt b (wrapperModule arithBase trieBase)) :
    MeetsContract w p (b + idxReadOutLimbs) (readOutLimbsContract w) := by
  refine readOutLimbs_meetsContract (mwFromHost_of_arithModule hArith)
    (trieRead_of_trieModule hArith hTrie) ?_
  have h := wrapperModule_procs_at hWrap (k := idxReadOutLimbs) (by rw [wrapperModule_length]; decide)
  simpa [wrapperModule, idxReadOutLimbs] using h

end MinCostFlow.WideWord