module

public import MinCostFlow.Basic.Dynamic
public import WordRAM.Memory

import Mathlib.Data.Finset.Card

/-!
# Dynamic named-graph (`MGraph`) and update-batch memory layouts

This file defines the Word-RAM memory layout for dynamic named graphs (`MGraph`) and update batches
(`Update`, `List Update`) from Section 2 (page 5) of the paper:

* `DynGraphAt mem a vCap eCap G`: in-place adjacency and sparse-set representation of `G : MGraph`
  at base address `a` occupying `dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap` words. It uses
  vertex-name/internal-slot indirection (`extToInt`, `intToExt`) and doubly-linked half-edge
  incidence lists (`incHead`, `hePrev`, `heNext`) so vertex splits run in time proportional to the
  smaller of the moved (`S`) or kept (`incident(v) \ S`) edge list.
* `IsDoublyLinkedList`: 1-indexed doubly-linked list invariant (`0 = NIL`, `h + 1` for half-edge
  `h`), with clean `cons` and `erase` preservation lemmas.
* `UpdateAt`, `BatchBodyAt`, `BatchAt`: variable-length encoding of `.insert`, `.delete`, and
  `.split` (both moved-set tag `2` and kept-set tag `3`) matching `MGraph.applyUpdate` and
  `MGraph.applyBatch`.
-/

namespace MinCostFlow.DynSpanner.Program

@[expose] public section

open WordRAM

/-! ## Dynamic graph layout constants -/

/-- Total memory footprint (in words) of `DynGraphAt mem a vCap eCap G`. -/
def dynGraphSize (vCap eCap : ℕ) : ℕ :=
  4 + 7 * vCap + 9 * eCap

/-- Header word offsets relative to the graph base pointer `a`. -/
def dgVCapOff : ℕ := 0
def dgECapOff : ℕ := 1
def dgNOff : ℕ := 2
def dgMOff : ℕ := 3
def dgHdrSize : ℕ := 4

/-- Vertex array base addresses (each array has length `vCap`). -/
def dgVPresBase (a : ℕ) : ℕ := a + 4
def dgVListBase (a vCap : ℕ) : ℕ := a + 4 + vCap
def dgVPosBase (a vCap : ℕ) : ℕ := a + 4 + 2 * vCap
def dgExtToIntBase (a vCap : ℕ) : ℕ := a + 4 + 3 * vCap
def dgIntToExtBase (a vCap : ℕ) : ℕ := a + 4 + 4 * vCap
def dgSlotDegBase (a vCap : ℕ) : ℕ := a + 4 + 5 * vCap
def dgIncHeadBase (a vCap : ℕ) : ℕ := a + 4 + 6 * vCap

/-- Edge and half-edge array base addresses (`eCap` or `2 * eCap` words). -/
def dgEPresBase (a vCap : ℕ) : ℕ := a + 4 + 7 * vCap
def dgEListBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + eCap
def dgEPosBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + 2 * eCap
def dgETailSlotBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + 3 * eCap
def dgEHeadSlotBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + 4 * eCap
def dgHePrevBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + 5 * eCap
def dgHeNextBase (a vCap eCap : ℕ) : ℕ := a + 4 + 7 * vCap + 7 * eCap

/-! ## Doubly-linked list invariant -/

/-- 1-indexed doubly-linked list of distinct elements `< cap`: `0` represents `NIL` and `h + 1`
represents element `h`. -/
def IsDoublyLinkedList (mem : ℕ → ℕ) (hePrevAddr heNextAddr headAddr cap : ℕ)
    (L : List ℕ) : Prop :=
  L.Nodup ∧
  (∀ h ∈ L, h < cap) ∧
  mem headAddr = (match L with | [] => 0 | h :: _ => h + 1) ∧
  ∀ i (hi : i < L.length),
    mem (hePrevAddr + L[i]) = (if i = 0 then 0 else L[i - 1] + 1) ∧
    mem (heNextAddr + L[i]) = (if i + 1 = L.length then 0 else L.getD (i + 1) 0 + 1)

/-! ## Dynamic graph layout predicate -/

/-- Full in-memory representation of a valid named graph `G : MGraph` with vertex capacity `vCap`
and edge capacity `eCap`, starting at address `a`. -/
def DynGraphAt (mem : ℕ → ℕ) (a vCap eCap : ℕ) (G : MGraph) : Prop :=
  G.IsValid ∧
  (∀ v ∈ G.V, v < vCap) ∧
  (∀ e ∈ G.E, e < eCap) ∧
  mem (a + dgVCapOff) = vCap ∧
  mem (a + dgECapOff) = eCap ∧
  mem (a + dgNOff) = G.n ∧
  mem (a + dgMOff) = G.m ∧
  (∀ v < vCap, mem (dgVPresBase a + v) = if v ∈ G.V then 1 else 0) ∧
  (∃ vL : List ℕ, vL.length = G.n ∧ vL.Nodup ∧ (∀ v, v ∈ vL ↔ v ∈ G.V) ∧
    ListAt mem (dgVListBase a vCap) vL ∧
    ∀ i (hi : i < vL.length), mem (dgVPosBase a vCap + vL[i]) = i) ∧
  (∀ v ∈ G.V,
    mem (dgExtToIntBase a vCap + v) ∈ G.V ∧
    mem (dgIntToExtBase a vCap + mem (dgExtToIntBase a vCap + v)) = v) ∧
  (∀ s ∈ G.V,
    mem (dgIntToExtBase a vCap + s) ∈ G.V ∧
    mem (dgExtToIntBase a vCap + mem (dgIntToExtBase a vCap + s)) = s) ∧
  (∀ e < eCap, mem (dgEPresBase a vCap + e) = if e ∈ G.E then 1 else 0) ∧
  (∃ eL : List ℕ, eL.length = G.m ∧ eL.Nodup ∧ (∀ e, e ∈ eL ↔ e ∈ G.E) ∧
    ListAt mem (dgEListBase a vCap eCap) eL ∧
    ∀ i (hi : i < eL.length), mem (dgEPosBase a vCap eCap + eL[i]) = i) ∧
  (∀ e ∈ G.E,
    mem (dgETailSlotBase a vCap eCap + e) = mem (dgExtToIntBase a vCap + G.tail e) ∧
    mem (dgEHeadSlotBase a vCap eCap + e) = mem (dgExtToIntBase a vCap + G.head e)) ∧
  (∃ incL : ℕ → List ℕ, ∀ s < vCap,
    IsDoublyLinkedList mem (dgHePrevBase a vCap eCap) (dgHeNextBase a vCap eCap)
      (dgIncHeadBase a vCap + s) (2 * eCap) (incL s) ∧
    mem (dgSlotDegBase a vCap + s) = (incL s).length ∧
    ∀ h, h ∈ incL s ↔
      h < 2 * eCap ∧ h / 2 ∈ G.E ∧
      (if h % 2 = 0 then mem (dgETailSlotBase a vCap eCap + h / 2)
       else mem (dgEHeadSlotBase a vCap eCap + h / 2)) = s)

/-! ## Update and batch layouts -/

/-- An encoded graph update at address `a` occupying `len` words relative to graph `G`:
- tag `0`: `[0, e, u, v]` (`len = 4`, `.insert e u v`)
- tag `1`: `[1, e]` (`len = 2`, `.delete e`)
- tag `2`: `[2, v, v', kt, kh] ++ Lt ++ Lh` (`len = 5 + kt + kh`, `.split v v' St Sh` with `Lt`
  enumerating moved tail ends at `v` and `Lh` enumerating moved head ends at `v`)
- tag `3`: `[3, v, v', kt, kh] ++ Lt ++ Lh` (`len = 5 + kt + kh`, `.split v v' St Sh` with `Lt`
  enumerating kept tail ends at `v` and `Lh` enumerating kept head ends at `v`). -/
def UpdateAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) (u : Update) (len : ℕ) : Prop :=
  match u with
  | .insert e x y => len = 4 ∧ ListAt mem a [0, e, x, y]
  | .delete e => len = 2 ∧ ListAt mem a [1, e]
  | .split v v' St Sh =>
    (∃ Lt Lh : List ℕ, Lt.Nodup ∧ Lh.Nodup ∧
      (∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∈ St) ∧
      (∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∈ Sh) ∧
      len = 5 + Lt.length + Lh.length ∧
      ListAt mem a ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)) ∨
    (∃ Lt Lh : List ℕ, Lt.Nodup ∧ Lh.Nodup ∧
      (∀ e, e ∈ Lt ↔ e ∈ G.E ∧ G.tail e = v ∧ e ∉ St) ∧
      (∀ e, e ∈ Lh ↔ e ∈ G.E ∧ G.head e = v ∧ e ∉ Sh) ∧
      len = 5 + Lt.length + Lh.length ∧
      ListAt mem a ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh))

/-- Sequential concatenation of encoded updates starting at address `a`. -/
def BatchBodyAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) : List Update → ℕ → Prop
  | [], totalWords => totalWords = 0
  | u :: us, totalWords =>
    ∃ len, len ≤ totalWords ∧ UpdateAt mem a G u len ∧
      BatchBodyAt mem (a + len) (G.applyUpdate u) us (totalWords - len)

/-- A batch of updates at address `a` occupying `totalWords` words: length header `U.length`
followed by `BatchBodyAt` starting at `a + 1`. -/
def BatchAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) (U : List Update) (totalWords : ℕ) : Prop :=
  1 ≤ totalWords ∧ mem a = U.length ∧ BatchBodyAt mem (a + 1) G U (totalWords - 1)

/-- Compact update encoding: word length is at most `G.updateEnc u + 4`. -/
def SmallUpdateAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) (u : Update) (len : ℕ) : Prop :=
  UpdateAt mem a G u len ∧ len ≤ G.updateEnc u + 4

/-- Compact batch encoding: total word length is at most `5 * G.batchEnc U + 1`. -/
def SmallBatchAt (mem : ℕ → ℕ) (a : ℕ) (G : MGraph) (U : List Update) (totalWords : ℕ) : Prop :=
  BatchAt mem a G U totalWords ∧ totalWords ≤ 5 * G.batchEnc U + 1

end

/-! ## Structural and frame lemmas -/

public section

open WordRAM

lemma IsDoublyLinkedList.nil {mem : ℕ → ℕ} {hePrevAddr heNextAddr headAddr cap : ℕ}
    (hhead : mem headAddr = 0) :
    IsDoublyLinkedList mem hePrevAddr heNextAddr headAddr cap [] := by
  refine ⟨List.nodup_nil, (fun _ h => by cases h), hhead, (fun i hi => by simp at hi)⟩

lemma IsDoublyLinkedList.of_agree {mem mem' : ℕ → ℕ}
    {hePrevAddr heNextAddr headAddr cap : ℕ} {L : List ℕ}
    (hL : IsDoublyLinkedList mem hePrevAddr heNextAddr headAddr cap L)
    (hhead : mem' headAddr = mem headAddr)
    (hp : ∀ h ∈ L, mem' (hePrevAddr + h) = mem (hePrevAddr + h))
    (hn : ∀ h ∈ L, mem' (heNextAddr + h) = mem (heNextAddr + h)) :
    IsDoublyLinkedList mem' hePrevAddr heNextAddr headAddr cap L := by
  rcases hL with ⟨hnd, hlt, hhd, hbody⟩
  refine ⟨hnd, hlt, hhead.trans hhd, fun i hi => ?_⟩
  have hm : L[i] ∈ L := List.getElem_mem hi
  have hb := hbody i hi
  exact ⟨(hp _ hm).trans hb.1, (hn _ hm).trans hb.2⟩

lemma IsDoublyLinkedList.head_eq_zero_iff {mem : ℕ → ℕ}
    {hePrevAddr heNextAddr headAddr cap : ℕ} {L : List ℕ}
    (hL : IsDoublyLinkedList mem hePrevAddr heNextAddr headAddr cap L) :
    mem headAddr = 0 ↔ L = [] := by
  cases L with
  | nil => simp [hL.2.2.1]
  | cons x xs => simp [hL.2.2.1]

lemma IsDoublyLinkedList.cons {mem mem' : ℕ → ℕ}
    {hePrevAddr heNextAddr headAddr cap h : ℕ} {L : List ℕ}
    (hL : IsDoublyLinkedList mem hePrevAddr heNextAddr headAddr cap L)
    (hh_lt : h < cap) (hh_not : h ∉ L)
    (hhead' : mem' headAddr = h + 1)
    (hp_h : mem' (hePrevAddr + h) = 0)
    (hn_h : mem' (heNextAddr + h) = mem headAddr)
    (hp_head : ∀ h₀ xs, L = h₀ :: xs → mem' (hePrevAddr + h₀) = h + 1)
    (hp_rest : ∀ y ∈ L, (∀ xs, L ≠ y :: xs) → mem' (hePrevAddr + y) = mem (hePrevAddr + y))
    (hn_rest : ∀ y ∈ L, mem' (heNextAddr + y) = mem (heNextAddr + y)) :
    IsDoublyLinkedList mem' hePrevAddr heNextAddr headAddr cap (h :: L) := by
  rcases hL with ⟨hnd, hlt, hhd, hbody⟩
  refine ⟨List.nodup_cons.mpr ⟨hh_not, hnd⟩, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hxL
    · exact hh_lt
    · exact hlt x hxL
  · simp [hhead']
  · intro i hi
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, ↓reduceIte, hp_h, true_and]
      cases L with
      | nil => rw [hn_h, hhd]; simp
      | cons h₀ xs =>
        simp only [List.length_cons, List.getD_cons_succ, List.getD_cons_zero] at hhd ⊢
        split_ifs with hzero
        · omega
        · rw [hn_h, hhd]
    | succ k =>
      have hk : k < L.length := Nat.lt_of_succ_lt_succ hi
      have hLk : L[k] ∈ L := List.getElem_mem hk
      have hb := hbody k hk
      simp only [List.getElem_cons_succ, List.length_cons, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_sub_cancel]
      refine ⟨?_, ?_⟩
      · cases k with
        | zero =>
          cases L with
          | nil => simp at hk
          | cons h₀ xs =>
            simp only [List.getElem_cons_zero]
            exact hp_head h₀ xs rfl
        | succ m =>
          have hm : m + 1 < L.length := hk
          have hne_head : ∀ xs, L ≠ L[m + 1] :: xs := by
            intro xs hEq
            have h0 : L[0] = L[m + 1] := by
              have hl : L = L[m + 1] :: xs := hEq
              calc L[0] = (L[m + 1] :: xs)[0] := by congr 1
                _ = L[m + 1] := rfl
            have hidx := hnd.getElem_inj_iff.mp h0
            omega
          rw [hp_rest _ hLk hne_head, hb.1]
          simp
      · rw [hn_rest _ hLk, hb.2]
        split_ifs with h1 h2 h2
        · rfl
        · omega
        · omega
        · simp

private lemma list_erase_getElem_of_nodup {α : Type*} [DecidableEq α] {L : List α}
    (hnd : L.Nodup) {k : ℕ} (hk : k < L.length) :
    L.erase L[k] = L.take k ++ L.drop (k + 1) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp [List.erase_cons_head]
    | succ m =>
      have hm : m < xs.length := Nat.lt_of_succ_lt_succ hk
      have hnd' := (List.nodup_cons.mp hnd)
      have hne : x ≠ xs[m] := fun hEq => hnd'.1 (hEq ▸ List.getElem_mem hm)
      simp only [List.getElem_cons_succ, List.erase_cons, beq_iff_eq, hne, ↓reduceIte,
        List.take_succ_cons, List.drop_succ_cons, List.cons_append]
      rw [ih hnd'.2 hm]

lemma IsDoublyLinkedList.erase {mem mem' : ℕ → ℕ}
    {hePrevAddr heNextAddr headAddr cap h : ℕ} {L : List ℕ}
    (hL : IsDoublyLinkedList mem hePrevAddr heNextAddr headAddr cap L)
    (hh_mem : h ∈ L)
    (h_head : ∀ y, y ∈ L.erase h →
      mem' headAddr = (if mem (hePrevAddr + h) = 0 then mem (heNextAddr + h) else mem headAddr))
    (h_head_empty : L.erase h = [] → mem' headAddr = 0)
    (hp_unchanged : ∀ y ∈ L.erase h,
      y ≠ (match L.idxOf h with
           | k => if hk1 : k + 1 < L.length then L[k + 1] else cap) →
      mem' (hePrevAddr + y) = mem (hePrevAddr + y))
    (hp_q : ∀ k (hk : k + 1 < L.length), L[k] = h →
      mem' (hePrevAddr + L[k + 1]) = mem (hePrevAddr + h))
    (hn_unchanged : ∀ y ∈ L.erase h,
      y ≠ (let k := L.idxOf h; if k = 0 then cap else L[k - 1]!) →
      mem' (heNextAddr + y) = mem (heNextAddr + y))
    (hn_p : ∀ k (hk : k < L.length) (hkpos : 0 < k), L[k] = h →
      mem' (heNextAddr + L[k - 1]) = mem (heNextAddr + h)) :
    IsDoublyLinkedList mem' hePrevAddr heNextAddr headAddr cap (L.erase h) := by
  classical
  rcases hL with ⟨hnd, hlt, hhd, hbody⟩
  obtain ⟨k, hk, hLk⟩ := List.getElem_of_mem hh_mem
  have hidx : L.idxOf h = k := by
    rw [← hLk]
    exact hnd.idxOf_getElem k hk
  have hErEq : L.erase h = L.take k ++ L.drop (k + 1) := by
    rw [← hLk]
    exact list_erase_getElem_of_nodup hnd hk
  have hLenEr : (L.erase h).length = L.length - 1 := by
    rw [List.length_erase_of_mem hh_mem]
  have hp_k := (hbody k hk).1
  have hn_k := (hbody k hk).2
  rw [hLk] at hp_k hn_k
  refine ⟨hnd.erase h, fun x hx => hlt x (List.mem_of_mem_erase hx), ?_, ?_⟩
  · cases hEr : L.erase h with
    | nil => exact h_head_empty hEr
    | cons y ys =>
      have hy_mem : y ∈ L.erase h := by simp [hEr]
      rw [h_head y hy_mem, hp_k, hn_k]
      have htake_drop := hErEq
      rw [hEr] at htake_drop
      cases k with
      | zero =>
        simp only [↓reduceIte, List.take_zero, List.nil_append, Nat.zero_add] at htake_drop ⊢
        have hk1 : 1 < L.length := by
          have : 0 < (L.drop 1).length := by rw [← htake_drop]; simp
          simp only [List.length_drop] at this; omega
        simp only [show ¬(0 + 1 = L.length) by omega, ↓reduceIte,
          List.getD_eq_getElem _ _ hk1]
        have hdrop1 : L.drop 1 = L[1] :: L.drop 2 := List.drop_eq_getElem_cons hk1
        rw [hdrop1] at htake_drop
        exact congrArg (· + 1) (List.cons.inj htake_drop).1.symm
      | succ m =>
        simp only [Nat.succ_ne_zero, ↓reduceIte]
        rcases List.exists_cons_of_ne_nil (show L ≠ [] by intro hn; subst hn; simp at hk) with
          ⟨z, zs, rfl⟩
        have htake : ((z :: zs).take (m + 1)).head? = some z := by
          simp [List.take_succ_cons]
        have hhead_er : ((z :: zs).take (m + 1) ++ (z :: zs).drop (m + 2)).head? = some z := by
          rw [List.head?_append, htake]; rfl
        rw [← htake_drop] at hhead_er
        simp only [List.head?_cons, Option.some.injEq] at hhead_er
        rw [hhd]
        exact congrArg (· + 1) hhead_er.symm
  · intro i hi
    have hi_len : i < L.length - 1 := hLenEr ▸ hi
    have hmem_er : (L.erase h)[i] ∈ L.erase h := List.getElem_mem hi
    have hEr_get : ∀ j (hj : j < L.length - 1),
        (L.erase h)[j]'(by omega) = if j < k then L[j] else L[j + 1] := by
      intro j hj
      have hlen_td : (L.take k ++ L.drop (k + 1)).length = L.length - 1 := by
        rw [← hErEq, hLenEr]
      trans (L.take k ++ L.drop (k + 1))[j]'(by omega)
      · congr 1
      · by_cases hjk : j < k
        · simp only [hjk, ↓reduceIte]
          rw [List.getElem_append_left (by simp [List.length_take]; omega), List.getElem_take]
        · simp only [hjk, ↓reduceIte]
          rw [List.getElem_append_right (by simp [List.length_take]; omega)]
          simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk), List.getElem_drop]
          congr 1; omega
    have hL_i : (L.erase h)[i] = if i < k then L[i] else L[i + 1] := hEr_get i hi_len
    refine ⟨?_, ?_⟩
    · by_cases hik : i = k
      · cases k with
        | zero =>
          subst hik
          simp only [↓reduceIte, Nat.lt_irrefl, Nat.zero_add] at hL_i ⊢
          have hk1 : 0 + 1 < L.length := by omega
          rw [hL_i, hp_q 0 hk1 hLk, hp_k]
          simp
        | succ m =>
          subst hik
          have hk1 : m + 1 + 1 < L.length := by omega
          simp only [Nat.lt_irrefl, ↓reduceIte] at hL_i
          rw [hL_i, hp_q (m + 1) hk1 hLk, hp_k]
          have him : m < (L.erase h).length := by omega
          simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ↓reduceIte]
          rw [hEr_get m (by omega)]
          simp [Nat.lt_succ_self m]
      · have hne_q : (L.erase h)[i] ≠
            (match L.idxOf h with | k' => if hk1 : k' + 1 < L.length then L[k' + 1] else cap) := by
          rw [hidx]
          dsimp only
          split_ifs with hk1
          · rw [hL_i]
            intro hEq
            by_cases hi_lt : i < k
            · simp only [hi_lt, ↓reduceIte] at hEq
              have hinj := hnd.getElem_inj_iff.mp hEq
              omega
            · simp only [hi_lt, ↓reduceIte] at hEq
              have hinj := hnd.getElem_inj_iff.mp hEq
              omega
          · exact Nat.ne_of_lt (hlt _ (List.mem_of_mem_erase hmem_er))
        rw [hp_unchanged _ hmem_er hne_q, hL_i]
        by_cases hi_lt : i < k
        · simp only [hi_lt, ↓reduceIte]
          rw [(hbody i (by omega)).1]
          cases i with
          | zero => simp
          | succ m =>
            simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            rw [hEr_get m (by omega)]
            simp [show m < k by omega]
        · have hik_gt : k < i := by omega
          simp only [hi_lt, ↓reduceIte]
          rw [(hbody (i + 1) (by omega)).1]
          have hi0 : i ≠ 0 := by omega
          simp only [hi0, Nat.succ_ne_zero, ↓reduceIte]
          rw [hEr_get (i - 1) (by omega)]
          simp only [show ¬(i - 1 < k) by omega, ↓reduceIte]
          congr 2; omega
    · by_cases hi1k : i + 1 = k
      · have hkpos : 0 < k := by omega
        have hEr_i : (L.erase h)[i] = L[k - 1] := by
          rw [hL_i]
          simp only [show i < k by omega, ↓reduceIte]
          congr 1; omega
        rw [hEr_i, hn_p k hk hkpos hLk, hn_k]
        split_ifs with h_er h_l
        · rfl
        · omega
        · omega
        · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
            hEr_get (i + 1) (by omega)]
          simp only [show ¬(i + 1 < k) by omega, ↓reduceIte]
          congr 2; omega
      · have hne_p : (L.erase h)[i] ≠ (let k' := L.idxOf h; if k' = 0 then cap else L[k' - 1]!) := by
          rw [hidx]
          by_cases hk0 : k = 0
          · simp only [hk0, ↓reduceIte]
            exact Nat.ne_of_lt (hlt _ (List.mem_of_mem_erase hmem_er))
          · simp only [hk0, ↓reduceIte, show L[k - 1]! = L[k - 1] from getElem!_pos L (k - 1) (by omega)]
            rw [hL_i]
            intro hEq
            by_cases hi_lt : i < k
            · simp only [hi_lt, ↓reduceIte] at hEq
              have hinj := hnd.getElem_inj_iff.mp hEq
              omega
            · simp only [hi_lt, ↓reduceIte] at hEq
              have hinj := hnd.getElem_inj_iff.mp hEq
              omega
        rw [hn_unchanged _ hmem_er hne_p, hL_i]
        by_cases hi_lt : i < k
        · simp only [hi_lt, ↓reduceIte]
          rw [(hbody i (by omega)).2]
          split_ifs with h_er h_l
          · rfl
          · omega
          · omega
          · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
              hEr_get (i + 1) (by omega)]
            simp [show i + 1 < k by omega]
        · simp only [hi_lt, ↓reduceIte]
          rw [(hbody (i + 1) (by omega)).2]
          split_ifs with h_er h_l
          · rfl
          · omega
          · omega
          · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
              hEr_get (i + 1) (by omega)]
            simp [show ¬(i + 1 < k) by omega]

/-- Any memory agreeing with `mem` on `[a, a + dynGraphSize vCap eCap)` preserves `DynGraphAt`. -/
lemma DynGraphAt.of_agree {mem mem' : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G)
    (hagree : ∀ addr, a ≤ addr → addr < a + dynGraphSize vCap eCap → mem' addr = mem addr) :
    DynGraphAt mem' a vCap eCap G := by
  have hmem : ∀ off, off < dynGraphSize vCap eCap → mem' (a + off) = mem (a + off) :=
    fun off hoff => hagree (a + off) (Nat.le_add_right _ _) (by omega)
  have hvp : ∀ v < vCap, mem' (dgVPresBase a + v) = mem (dgVPresBase a + v) := fun v hv => by
    simpa [dgVPresBase, Nat.add_assoc] using hmem (4 + v) (by simp [dynGraphSize]; omega)
  have hvl : ∀ i < vCap, mem' (dgVListBase a vCap + i) = mem (dgVListBase a vCap + i) :=
    fun i hi => by
      simpa [dgVListBase, Nat.add_assoc] using hmem (4 + vCap + i) (by simp [dynGraphSize]; omega)
  have hvpos : ∀ v < vCap, mem' (dgVPosBase a vCap + v) = mem (dgVPosBase a vCap + v) :=
    fun v hv => by
      simpa [dgVPosBase, Nat.add_assoc] using hmem (4 + 2 * vCap + v) (by simp [dynGraphSize]; omega)
  have heti : ∀ v < vCap, mem' (dgExtToIntBase a vCap + v) = mem (dgExtToIntBase a vCap + v) :=
    fun v hv => by
      simpa [dgExtToIntBase, Nat.add_assoc] using hmem (4 + 3 * vCap + v) (by simp [dynGraphSize]; omega)
  have hite : ∀ s < vCap, mem' (dgIntToExtBase a vCap + s) = mem (dgIntToExtBase a vCap + s) :=
    fun s hs => by
      simpa [dgIntToExtBase, Nat.add_assoc] using hmem (4 + 4 * vCap + s) (by simp [dynGraphSize]; omega)
  have hsdeg : ∀ s < vCap, mem' (dgSlotDegBase a vCap + s) = mem (dgSlotDegBase a vCap + s) :=
    fun s hs => by
      simpa [dgSlotDegBase, Nat.add_assoc] using hmem (4 + 5 * vCap + s) (by simp [dynGraphSize]; omega)
  have hihd : ∀ s < vCap, mem' (dgIncHeadBase a vCap + s) = mem (dgIncHeadBase a vCap + s) :=
    fun s hs => by
      simpa [dgIncHeadBase, Nat.add_assoc] using hmem (4 + 6 * vCap + s) (by simp [dynGraphSize]; omega)
  have hep : ∀ e < eCap, mem' (dgEPresBase a vCap + e) = mem (dgEPresBase a vCap + e) :=
    fun e he => by
      simpa [dgEPresBase, Nat.add_assoc] using hmem (4 + 7 * vCap + e) (by simp [dynGraphSize]; omega)
  have hel : ∀ i < eCap, mem' (dgEListBase a vCap eCap + i) = mem (dgEListBase a vCap eCap + i) :=
    fun i hi => by
      simpa [dgEListBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + eCap + i) (by simp [dynGraphSize]; omega)
  have hepos : ∀ e < eCap, mem' (dgEPosBase a vCap eCap + e) = mem (dgEPosBase a vCap eCap + e) :=
    fun e he => by
      simpa [dgEPosBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + 2 * eCap + e) (by simp [dynGraphSize]; omega)
  have hets : ∀ e < eCap, mem' (dgETailSlotBase a vCap eCap + e) = mem (dgETailSlotBase a vCap eCap + e) :=
    fun e he => by
      simpa [dgETailSlotBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + 3 * eCap + e) (by simp [dynGraphSize]; omega)
  have hehs : ∀ e < eCap, mem' (dgEHeadSlotBase a vCap eCap + e) = mem (dgEHeadSlotBase a vCap eCap + e) :=
    fun e he => by
      simpa [dgEHeadSlotBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + 4 * eCap + e) (by simp [dynGraphSize]; omega)
  have hhp : ∀ h < 2 * eCap, mem' (dgHePrevBase a vCap eCap + h) = mem (dgHePrevBase a vCap eCap + h) :=
    fun h hh => by
      simpa [dgHePrevBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + 5 * eCap + h) (by simp [dynGraphSize]; omega)
  have hhn : ∀ h < 2 * eCap, mem' (dgHeNextBase a vCap eCap + h) = mem (dgHeNextBase a vCap eCap + h) :=
    fun h hh => by
      simpa [dgHeNextBase, Nat.add_assoc] using
        hmem (4 + 7 * vCap + 7 * eCap + h) (by simp [dynGraphSize]; omega)
  rcases hG with ⟨hval, hvCap, heCap, h0, h1, h2, h3, hvp0, ⟨vL, hvL_len, hvL_nd, hvL_mem,
    hvL_at, hvL_pos⟩, heti0, hite0, hep0, ⟨eL, heL_len, heL_nd, heL_mem, heL_at, heL_pos⟩,
    hets_ehs, ⟨incL, hincL⟩⟩
  refine ⟨hval, hvCap, heCap, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [dgVCapOff] using (hmem 0 (by dsimp [dynGraphSize]; omega)).trans h0
  · simpa [dgECapOff] using (hmem 1 (by dsimp [dynGraphSize]; omega)).trans h1
  · simpa [dgNOff] using (hmem 2 (by dsimp [dynGraphSize]; omega)).trans h2
  · simpa [dgMOff] using (hmem 3 (by dsimp [dynGraphSize]; omega)).trans h3
  · intro v hv; exact (hvp v hv).trans (hvp0 v hv)
  · refine ⟨vL, hvL_len, hvL_nd, hvL_mem, ?_, ?_⟩
    · intro i hi
      have hvi_lt : vL[i] < vCap := hvCap _ ((hvL_mem _).mp (List.getElem_mem hi))
      have _ := hvi_lt
      have hi_lt : i < vCap := by
        have hsub : vL.toFinset ⊆ Finset.range vCap := by
          intro x hx; rw [Finset.mem_range]; exact hvCap x ((hvL_mem x).mp (List.mem_toFinset.mp hx))
        have hcard : vL.length ≤ vCap := by
          rw [← List.toFinset_card_of_nodup hvL_nd]
          simpa using Finset.card_le_card hsub
        omega
      exact (hvl i hi_lt).trans (hvL_at i hi)
    · intro i hi
      have hvi_lt : vL[i] < vCap := hvCap _ ((hvL_mem _).mp (List.getElem_mem hi))
      exact (hvpos _ hvi_lt).trans (hvL_pos i hi)
  · intro v hv
    have hv_lt := hvCap v hv
    rcases heti0 v hv with ⟨hsV, hinv⟩
    rw [heti v hv_lt]
    exact ⟨hsV, (hite _ (hvCap _ hsV)).trans hinv⟩
  · intro s hs
    have hs_lt := hvCap s hs
    rcases hite0 s hs with ⟨hvV, hinv⟩
    rw [hite s hs_lt]
    exact ⟨hvV, (heti _ (hvCap _ hvV)).trans hinv⟩
  · intro e he; exact (hep e he).trans (hep0 e he)
  · refine ⟨eL, heL_len, heL_nd, heL_mem, ?_, ?_⟩
    · intro i hi
      have hsub : eL.toFinset ⊆ Finset.range eCap := by
        intro x hx; rw [Finset.mem_range]; exact heCap x ((heL_mem x).mp (List.mem_toFinset.mp hx))
      have hcard : eL.length ≤ eCap := by
        rw [← List.toFinset_card_of_nodup heL_nd]
        simpa using Finset.card_le_card hsub
      exact (hel i (by omega)).trans (heL_at i hi)
    · intro i hi
      exact (hepos _ (heCap _ ((heL_mem _).mp (List.getElem_mem hi)))).trans (heL_pos i hi)
  · intro e he
    rcases hets_ehs e he with ⟨ht, hh⟩
    rcases hval e he with ⟨htV, hhV⟩
    refine ⟨(hets e (heCap e he)).trans (ht.trans (heti _ (hvCap _ htV)).symm),
      (hehs e (heCap e he)).trans (hh.trans (heti _ (hvCap _ hhV)).symm)⟩
  · refine ⟨incL, fun s hs => ?_⟩
    rcases hincL s hs with ⟨hdll, hdeg, hmem_iff⟩
    refine ⟨hdll.of_agree (hihd s hs) (fun h hh => hhp h (hdll.2.1 h hh))
        (fun h hh => hhn h (hdll.2.1 h hh)), (hsdeg s hs).trans hdeg, fun h => ?_⟩
    rw [hmem_iff h]
    constructor
    · rintro ⟨hh2, heE, hslot⟩
      refine ⟨hh2, heE, ?_⟩
      have he_cap : h / 2 < eCap := by omega
      split_ifs at hslot ⊢
      · exact (hets _ he_cap).trans hslot
      · exact (hehs _ he_cap).trans hslot
    · rintro ⟨hh2, heE, hslot⟩
      refine ⟨hh2, heE, ?_⟩
      have he_cap : h / 2 < eCap := by omega
      split_ifs at hslot ⊢
      · exact (hets _ he_cap).symm.trans hslot
      · exact (hehs _ he_cap).symm.trans hslot

/-- `slotDeg[extToInt[v]]` equals `G.deg v` for every vertex `v ∈ G.V`. -/
lemma DynGraphAt.slotDeg_eq_deg {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {v : ℕ} (hv : v ∈ G.V) :
    mem (dgSlotDegBase a vCap + mem (dgExtToIntBase a vCap + v)) = G.deg v := by
  rcases hG with ⟨hval, hvCap, heCap, _, _, _, _, _, _, heti0, _, _, _, hets_ehs, ⟨incL, hincL⟩⟩
  set s := mem (dgExtToIntBase a vCap + v)
  have hsV : s ∈ G.V := (heti0 v hv).1
  have hs_cap : s < vCap := hvCap s hsV
  rcases hincL s hs_cap with ⟨hdll, hsdeg, hmem_iff⟩
  rw [hsdeg, ← List.toFinset_card_of_nodup hdll.1]
  let E_t := G.E.filter fun e => G.tail e = v
  let E_h := G.E.filter fun e => G.head e = v
  have hS_eq : (incL s).toFinset =
      (E_t.image (fun e => 2 * e)) ∪ (E_h.image (fun e => 2 * e + 1)) := by
    ext h
    simp only [List.mem_toFinset, hmem_iff, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, E_t, E_h]
    constructor
    · rintro ⟨hh2, heE, hslot⟩
      have he_cap := heCap _ heE
      rcases hets_ehs _ heE with ⟨ht_eq, hh_eq⟩
      rcases hval _ heE with ⟨htV, hhV⟩
      by_cases heven : h % 2 = 0
      · left
        refine ⟨h / 2, ⟨heE, ?_⟩, by omega⟩
        simp only [heven, ↓reduceIte] at hslot
        rw [ht_eq] at hslot
        have hinj := congrArg (fun x => mem (dgIntToExtBase a vCap + x)) hslot
        rw [(heti0 _ htV).2, (heti0 v hv).2] at hinj
        exact hinj
      · right
        refine ⟨h / 2, ⟨heE, ?_⟩, by omega⟩
        simp only [heven, ↓reduceIte] at hslot
        rw [hh_eq] at hslot
        have hinj := congrArg (fun x => mem (dgIntToExtBase a vCap + x)) hslot
        rw [(heti0 _ hhV).2, (heti0 v hv).2] at hinj
        exact hinj
    · rintro (⟨e, ⟨heE, ht_eq⟩, rfl⟩ | ⟨e, ⟨heE, hh_eq⟩, rfl⟩)
      · have he_cap := heCap e heE
        have hdiv : 2 * e / 2 = e := by omega
        refine ⟨by omega, by rwa [hdiv], ?_⟩
        simp only [show 2 * e % 2 = 0 by omega, ↓reduceIte, hdiv, (hets_ehs e heE).1, ht_eq]
        rfl
      · have he_cap := heCap e heE
        have hdiv : (2 * e + 1) / 2 = e := by omega
        refine ⟨by omega, by rwa [hdiv], ?_⟩
        simp only [show (2 * e + 1) % 2 ≠ 0 by omega, ↓reduceIte, hdiv, (hets_ehs e heE).2, hh_eq]
        rfl
  rw [hS_eq, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ (fun x y hxy => by omega),
        Finset.card_image_of_injective _ (fun x y hxy => by omega)]
    rfl
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image] at hx hy
    rcases hx with ⟨e₁, _, rfl⟩
    rcases hy with ⟨e₂, _, hEq⟩
    omega

lemma DynGraphAt.slotDeg_zero_of_not_mem {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {s : ℕ} (hs : s < vCap) (hsV : s ∉ G.V) :
    mem (dgSlotDegBase a vCap + s) = 0 ∧ mem (dgIncHeadBase a vCap + s) = 0 := by
  rcases hG with ⟨hval, _, _, _, _, _, _, _, _, heti0, _, _, _, hets_ehs, ⟨incL, hincL⟩⟩
  rcases hincL s hs with ⟨hdll, hsdeg, hmem_iff⟩
  have hnil : incL s = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro h hh
    rcases (hmem_iff h).mp hh with ⟨_, heE, hslot⟩
    rcases hets_ehs _ heE with ⟨ht, hh_⟩
    rcases hval _ heE with ⟨htV, hhV⟩
    split_ifs at hslot
    · rw [ht] at hslot; exact hsV (hslot ▸ (heti0 _ htV).1)
    · rw [hh_] at hslot; exact hsV (hslot ▸ (heti0 _ hhV).1)
  have hhd := hdll.2.2.1
  rw [hnil] at hsdeg hhd
  simpa using ⟨hsdeg, hhd⟩

private lemma listAt_zero_getElemD (L : List ℕ) :
    ListAt (fun i => L[i]?.getD 0) 0 L := by
  intro i hi
  simp [List.getElem?_eq_getElem hi]

/-- Every valid graph update has a small Word-RAM encoding of length at most `G.updateEnc u + 4`. -/
lemma exists_small_updateAt {G : MGraph} {u : Update} (hu : G.UpdateIsValid u) :
    ∃ len mem, SmallUpdateAt mem 0 G u len := by
  cases u with
  | insert e x y =>
    exact ⟨4, fun i => [0, e, x, y][i]?.getD 0,
      ⟨⟨rfl, listAt_zero_getElemD [0, e, x, y]⟩, by simp [MGraph.updateEnc]⟩⟩
  | delete e =>
    exact ⟨2, fun i => [1, e][i]?.getD 0,
      ⟨⟨rfl, listAt_zero_getElemD [1, e]⟩, by simp [MGraph.updateEnc]⟩⟩
  | split v v' St Sh =>
    let G' := G.applyUpdate (.split v v' St Sh)
    by_cases hcmp : G'.deg v' ≤ G'.deg v
    · set Kt := G.E.filter fun e => G.tail e = v ∧ e ∈ St
      set Kh := G.E.filter fun e => G.head e = v ∧ e ∈ Sh
      set Lt := Kt.toList
      set Lh := Kh.toList
      refine ⟨5 + Lt.length + Lh.length,
        fun i => ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[i]?.getD 0,
        Or.inl ⟨Lt, Lh, Finset.nodup_toList Kt, Finset.nodup_toList Kh,
          fun e => by simp [Lt, Kt],
          fun e => by simp [Lh, Kh],
          rfl, listAt_zero_getElemD ([2, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)⟩, ?_⟩
      have hKt_sub : Kt ⊆ G'.E.filter (fun e => G'.tail e = v') := by
        intro e he
        simp only [Kt, Finset.mem_filter] at he
        simp only [Finset.mem_filter, G', MGraph.applyUpdate, he.1, he.2.1, he.2.2, and_self,
          ↓reduceIte]
      have hKh_sub : Kh ⊆ G'.E.filter (fun e => G'.head e = v') := by
        intro e he
        simp only [Kh, Finset.mem_filter] at he
        simp only [Finset.mem_filter, G', MGraph.applyUpdate, he.1, he.2.1, he.2.2, and_self,
          ↓reduceIte]
      have hcard : Kt.card + Kh.card ≤ G'.deg v' := by
        calc Kt.card + Kh.card
            ≤ (G'.E.filter (fun e => G'.tail e = v')).card +
              (G'.E.filter (fun e => G'.head e = v')).card :=
              Nat.add_le_add (Finset.card_le_card hKt_sub) (Finset.card_le_card hKh_sub)
          _ = G'.deg v' := rfl
      have hlent : Lt.length = Kt.card := Finset.length_toList Kt
      have hlenh : Lh.length = Kh.card := Finset.length_toList Kh
      have hmin : G.updateEnc (.split v v' St Sh) = min (G'.deg v) (G'.deg v') + 1 := rfl
      rw [hmin, min_eq_right hcmp]
      omega
    · set Kt := G.E.filter fun e => G.tail e = v ∧ e ∉ St
      set Kh := G.E.filter fun e => G.head e = v ∧ e ∉ Sh
      set Lt := Kt.toList
      set Lh := Kh.toList
      refine ⟨5 + Lt.length + Lh.length,
        fun i => ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)[i]?.getD 0,
        Or.inr ⟨Lt, Lh, Finset.nodup_toList Kt, Finset.nodup_toList Kh,
          fun e => by simp [Lt, Kt],
          fun e => by simp [Lh, Kh],
          rfl, listAt_zero_getElemD ([3, v, v', Lt.length, Lh.length] ++ Lt ++ Lh)⟩, ?_⟩
      have hKt_sub : Kt ⊆ G'.E.filter (fun e => G'.tail e = v) := by
        intro e he
        simp only [Kt, Finset.mem_filter] at he
        simp only [Finset.mem_filter, G', MGraph.applyUpdate, he.1, he.2.1, he.2.2,
          false_and, ↓reduceIte, and_self]
      have hKh_sub : Kh ⊆ G'.E.filter (fun e => G'.head e = v) := by
        intro e he
        simp only [Kh, Finset.mem_filter] at he
        simp only [Finset.mem_filter, G', MGraph.applyUpdate, he.1, he.2.1, he.2.2,
          false_and, ↓reduceIte, and_self]
      have hcard : Kt.card + Kh.card ≤ G'.deg v := by
        calc Kt.card + Kh.card
            ≤ (G'.E.filter (fun e => G'.tail e = v)).card +
              (G'.E.filter (fun e => G'.head e = v)).card :=
              Nat.add_le_add (Finset.card_le_card hKt_sub) (Finset.card_le_card hKh_sub)
          _ = G'.deg v := rfl
      have hlt : G'.deg v ≤ G'.deg v' := le_of_not_ge hcmp
      have hlent : Lt.length = Kt.card := Finset.length_toList Kt
      have hlenh : Lh.length = Kh.card := Finset.length_toList Kh
      have hmin : G.updateEnc (.split v v' St Sh) = min (G'.deg v) (G'.deg v') + 1 := rfl
      rw [hmin, min_eq_left hlt]
      omega

end

end MinCostFlow.DynSpanner.Program
