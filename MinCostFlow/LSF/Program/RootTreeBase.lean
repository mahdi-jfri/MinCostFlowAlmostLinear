module

public import MinCostFlow.LSF.Program.KeyedSort
public import WordRAM.Tactic
import Mathlib.Tactic.Linarith

/-!
# Rooting a tree by breadth-first search: definitions

The initialization of Lemma 5.4 (page 17) roots the low-stretch tree `T₀` at `r₀` and stores,
for every vertex, its parent, the tree edge to the parent and its depth (the arrays `t0Parent`,
`t0ParentTreeIdx` and `t0Depth` of `AuxAt`). This file sets up the procedure `rootTreeProc`
that does this in time `O(n + m)` for a graph on the vertices `0, …, n - 1` given by two arrays
of endpoints.

The procedure first builds, for every vertex, a singly linked list of its half-edges (half-edge
`2 f` is the tail end of edge `f`, half-edge `2 f + 1` its head end). It then runs a
breadth-first search from `r`. When the search first reaches a vertex `x` from `u` along edge
`f`, it records `u`, `f` and the depth of `u` plus one.

Here we define the abstract objects: the endpoint of a half-edge, the list of half-edges at a
vertex, the stored linked lists (`ChainFrom`), the adjacency relation, and the procedure text.
-/

namespace MinCostFlow.LSF.Program

open WordRAM

@[expose] public section

/-! ## Half-edges and adjacency -/

/-- The endpoint of half-edge `h`: the tail of edge `h / 2` for even `h`, its head for odd `h`. -/
def rtEnd (tl hd : ℕ → ℕ) (h : ℕ) : ℕ := if h % 2 = 0 then tl (h / 2) else hd (h / 2)

/-- The other endpoint of the edge of half-edge `h`. -/
def rtOther (tl hd : ℕ → ℕ) (h : ℕ) : ℕ := if h % 2 = 0 then hd (h / 2) else tl (h / 2)

/-- The half-edges `h < k` at vertex `u`, latest first. -/
def rtHalf (tl hd : ℕ → ℕ) (k u : ℕ) : List ℕ :=
  ((List.range k).filter (fun h => rtEnd tl hd h = u)).reverse

/-- Two vertices are adjacent when some edge `f < m` joins them. -/
def rtAdj (m : ℕ) (tl hd : ℕ → ℕ) (u x : ℕ) : Prop :=
  ∃ f < m, (tl f = u ∧ hd f = x) ∨ (hd f = u ∧ tl f = x)

/-- The number of half-edges at `u` among the `2 m` half-edges. -/
def rtDeg (m : ℕ) (tl hd : ℕ → ℕ) (u : ℕ) : ℕ := (rtHalf tl hd (2 * m) u).length

lemma rtHalf_succ (tl hd : ℕ → ℕ) (k u : ℕ) :
    rtHalf tl hd (k + 1) u = if rtEnd tl hd k = u then k :: rtHalf tl hd k u
      else rtHalf tl hd k u := by
  unfold rtHalf
  rw [List.range_succ, List.filter_append]
  by_cases h : rtEnd tl hd k = u <;> simp [h]

lemma mem_rtHalf {tl hd : ℕ → ℕ} {k u h : ℕ} :
    h ∈ rtHalf tl hd k u ↔ h < k ∧ rtEnd tl hd h = u := by
  simp [rtHalf]

lemma rtHalf_nodup (tl hd : ℕ → ℕ) (k u : ℕ) : (rtHalf tl hd k u).Nodup := by
  unfold rtHalf
  exact List.nodup_reverse.mpr ((List.nodup_range).filter _)

/-- An edge `f < m` gives a half-edge at `u` whose other end is `x`, and conversely. -/
lemma rtAdj_iff {m : ℕ} {tl hd : ℕ → ℕ} {u x : ℕ} :
    rtAdj m tl hd u x ↔ ∃ h ∈ rtHalf tl hd (2 * m) u, rtOther tl hd h = x := by
  constructor
  · rintro ⟨f, hf, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨2 * f, mem_rtHalf.mpr ⟨by omega, ?_⟩, ?_⟩
      · simp [rtEnd, h1]
      · simp [rtOther, h2]
    · refine ⟨2 * f + 1, mem_rtHalf.mpr ⟨by omega, ?_⟩, ?_⟩
      · have h3 : (2 * f + 1) % 2 = 1 := by omega
        have h4 : (2 * f + 1) / 2 = f := by omega
        simp [rtEnd, h3, h4, h1]
      · have h3 : (2 * f + 1) % 2 = 1 := by omega
        have h4 : (2 * f + 1) / 2 = f := by omega
        simp [rtOther, h3, h4, h2]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hlt, hend⟩ := mem_rtHalf.mp hh
    refine ⟨h / 2, by omega, ?_⟩
    by_cases hp : h % 2 = 0
    · left; simp only [rtEnd, rtOther, hp, ↓reduceIte] at hend ⊢; exact ⟨hend, trivial⟩
    · right; simp only [rtEnd, rtOther, hp, ↓reduceIte] at hend ⊢; exact ⟨hend, trivial⟩

/-- The degrees of distinct vertices add up to at most the number `2 m` of half-edges. -/
lemma rtDeg_sum_le {m : ℕ} {tl hd : ℕ → ℕ} :
    ∀ {L : List ℕ}, L.Nodup → (L.map (rtDeg m tl hd)).sum ≤ 2 * m := by
  intro L hL
  classical
  have hcard : ∀ u, rtDeg m tl hd u =
      ((Finset.range (2 * m)).filter (fun h => rtEnd tl hd h = u)).card := by
    intro u
    unfold rtDeg rtHalf
    rw [List.length_reverse, ← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
    congr 1
    ext h
    simp
  have hsum : (L.map (rtDeg m tl hd)).sum =
      ∑ u ∈ L.toFinset, ((Finset.range (2 * m)).filter (fun h => rtEnd tl hd h = u)).card := by
    rw [List.sum_toFinset _ hL]
    exact congrArg List.sum (List.map_congr_left fun u _ => hcard u)
  rw [hsum, ← Finset.card_biUnion]
  · calc _ ≤ (Finset.range (2 * m)).card := by
          apply Finset.card_le_card
          intro h hh
          simp only [Finset.mem_biUnion, Finset.mem_filter] at hh
          obtain ⟨_, _, hr, _⟩ := hh
          exact hr
      _ = 2 * m := Finset.card_range _
  · intro u _ v _ huv
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact huv (h1.2.symm.trans h2.2)

/-! ## Linked lists of half-edges in memory -/

/-- The linked list starting at pointer `p` lists the half-edges `L`. A pointer is `h + 1` for
half-edge `h`, and `0` ends the list; the successor of `h` is stored at `next + h`. -/
def ChainFrom (mem : ℕ → ℕ) (next : ℕ) : ℕ → List ℕ → Prop
  | p, [] => p = 0
  | p, h :: L => p = h + 1 ∧ ChainFrom mem next (mem (next + h)) L

lemma ChainFrom.congr {mem mem' : ℕ → ℕ} {next : ℕ} :
    ∀ {p : ℕ} {L : List ℕ}, ChainFrom mem next p L →
      (∀ h ∈ L, mem' (next + h) = mem (next + h)) → ChainFrom mem' next p L
  | _, [], h, _ => h
  | _, x :: L, ⟨hp, hrest⟩, hag => by
    refine ⟨hp, ?_⟩
    rw [hag x (by simp)]
    exact ChainFrom.congr hrest fun h hh => hag h (List.mem_cons_of_mem _ hh)

/-- Prepending half-edge `k` at vertex `v`: set `next[k]` to the old head and the head of `v`
to `k + 1`. Afterwards the lists are those of the half-edges `h < k + 1`. -/
lemma chainFrom_insert {mem : ℕ → ℕ} {tl hd : ℕ → ℕ} {first next n k v : ℕ}
    (hall : ∀ u < n, ChainFrom mem next (mem (first + u)) (rtHalf tl hd k u))
    (hv : rtEnd tl hd k = v) (hvn : v < n) (hlay : first + n ≤ next) :
    let mem' := Function.update (Function.update mem (next + k) (mem (first + v)))
      (first + v) (k + 1)
    ∀ u < n, ChainFrom mem' next (mem' (first + u)) (rtHalf tl hd (k + 1) u) := by
  intro mem' u hu
  have hag : ∀ u < n, ∀ h ∈ rtHalf tl hd k u, mem' (next + h) = mem (next + h) := by
    intro u _ h hh
    have hlt := (mem_rtHalf.mp hh).1
    simp only [mem']
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  rw [rtHalf_succ]
  by_cases huv : u = v
  · subst huv
    simp only [hv, ↓reduceIte]
    refine ⟨by simp [mem'], ?_⟩
    have h1 : mem' (next + k) = mem (first + rtEnd tl hd k) := by
      simp only [mem']
      rw [Function.update_of_ne (by omega), Function.update_self, hv]
    rw [h1, hv]
    exact (hall _ hu).congr (hag _ hu)
  · have hne : rtEnd tl hd k ≠ u := fun h => huv (h.symm.trans hv)
    simp only [hne, ↓reduceIte]
    have h1 : mem' (first + u) = mem (first + u) := by
      simp only [mem']
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    rw [h1]
    exact (hall u hu).congr (hag u hu)

/-! ## The procedure -/

/-- Phase 1, edge `f` (register 12): prepend half-edge `2 f` at its tail and `2 f + 1` at its
head. -/
def rtBuildBody : Stmt :=
  .assign 13 (.load (.bin .add (.reg 2) (.reg 12))) ;;
  .store (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 12)))
    (.load (.bin .add (.reg 6) (.reg 13))) ;;
  .store (.bin .add (.reg 6) (.reg 13)) (.bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1)) ;;
  .assign 13 (.load (.bin .add (.reg 3) (.reg 12))) ;;
  .store (.bin .add (.reg 9) (.bin .add (.bin .mul (.const 2) (.reg 12)) (.const 1)))
    (.load (.bin .add (.reg 6) (.reg 13))) ;;
  .store (.bin .add (.reg 6) (.reg 13)) (.bin .add (.bin .mul (.const 2) (.reg 12)) (.const 2))

/-- Visit vertex `x` (register 20) reached from `u` (register 16) along edge `f` (register 19),
if it is not visited yet. -/
def rtVisit : Stmt :=
  .cond (.bin .eq (.load (.bin .add (.reg 10) (.reg 20))) (.const 0))
    (.store (.bin .add (.reg 10) (.reg 20)) (.const 1) ;;
     .store (.bin .add (.reg 11) (.reg 15)) (.reg 20) ;;
     .assign 15 (.bin .add (.reg 15) (.const 1)) ;;
     .store (.bin .add (.reg 5) (.reg 20)) (.reg 16) ;;
     .store (.bin .add (.reg 7) (.reg 20)) (.reg 19) ;;
     .store (.bin .add (.reg 8) (.reg 20))
       (.bin .add (.load (.bin .add (.reg 8) (.reg 16))) (.const 1)))
    .nop

/-- One step of the scan of the half-edges at `u`: pointer `p` (register 17). -/
def rtScanBody : Stmt :=
  .assign 18 (.bin .sub (.reg 17) (.const 1)) ;;
  .assign 19 (.bin .div (.reg 18) (.const 2)) ;;
  .assign 17 (.load (.bin .add (.reg 9) (.reg 18))) ;;
  .cond (.bin .eq (.bin .mod (.reg 18) (.const 2)) (.const 0))
    (.assign 20 (.load (.bin .add (.reg 3) (.reg 19))))
    (.assign 20 (.load (.bin .add (.reg 2) (.reg 19)))) ;;
  rtVisit

/-- One step of the search: take the next vertex `u` of the queue and scan its half-edges. -/
def rtBfsBody : Stmt :=
  .assign 16 (.load (.bin .add (.reg 11) (.reg 14))) ;;
  .assign 14 (.bin .add (.reg 14) (.const 1)) ;;
  .assign 17 (.load (.bin .add (.reg 6) (.reg 16))) ;;
  .loop (.reg 17) rtScanBody

/-- Root the graph on `0, …, n - 1` with edges `f < m` from `tail[f]` to `head[f]` at `r`.
Args: `[n, m, tailArr, headArr, r, outPtr, scratchPtr]`. Writes parents at `outPtr`, parent
edges at `outPtr + n`, depths at `outPtr + 2 n`, and uses `4 n + 2 m` zeroed scratch words. -/
def rootTreeProc : Stmt :=
  .assign 7 (.bin .add (.reg 5) (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 0)) ;;
  .assign 9 (.bin .add (.reg 6) (.reg 0)) ;;
  .assign 10 (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 1))) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 0)) ;;
  forRange 12 (.const 0) (.reg 1) rtBuildBody ;;
  .store (.bin .add (.reg 10) (.reg 4)) (.const 1) ;;
  .store (.reg 11) (.reg 4) ;;
  .store (.bin .add (.reg 5) (.reg 4)) (.reg 4) ;;
  .store (.bin .add (.reg 7) (.reg 4)) (.const 0) ;;
  .store (.bin .add (.reg 8) (.reg 4)) (.const 0) ;;
  .assign 14 (.const 0) ;;
  .assign 15 (.const 1) ;;
  .loop (.bin .lt (.reg 14) (.reg 15)) rtBfsBody ;;
  .ret (.const 0)

lemma rootTreeProc_noRand : rootTreeProc.NoRand := by
  simp [rootTreeProc, rtBfsBody, rtScanBody, rtVisit, rtBuildBody, forRange, forUp, Stmt.NoRand]

/-! ## Fixed registers -/

/-- Registers `0, …, 11` during the run: the arguments and the derived array bases. -/
structure RTRegs (st : State) (n m tailArr headArr r outPtr sPtr : ℕ) : Prop where
  r0 : st.regs 0 = n
  r1 : st.regs 1 = m
  r2 : st.regs 2 = tailArr
  r3 : st.regs 3 = headArr
  r4 : st.regs 4 = r
  r5 : st.regs 5 = outPtr
  r6 : st.regs 6 = sPtr
  r7 : st.regs 7 = outPtr + n
  r8 : st.regs 8 = outPtr + n + n
  r9 : st.regs 9 = sPtr + n
  r10 : st.regs 10 = sPtr + n + 2 * m
  r11 : st.regs 11 = sPtr + n + 2 * m + n

lemma RTRegs.upd {st : State} {n m tailArr headArr r outPtr sPtr : ℕ}
    (hb : RTRegs st n m tailArr headArr r outPtr sPtr) (q v : ℕ) (hq : 12 ≤ q) :
    RTRegs { st with regs := Function.update st.regs q v } n m tailArr headArr r outPtr sPtr := by
  have h : ∀ i, i < 12 → Function.update st.regs q v i = st.regs i :=
    fun i hi => Function.update_of_ne (by omega) _ _
  exact ⟨(h 0 (by omega)).trans hb.r0, (h 1 (by omega)).trans hb.r1, (h 2 (by omega)).trans hb.r2,
    (h 3 (by omega)).trans hb.r3, (h 4 (by omega)).trans hb.r4, (h 5 (by omega)).trans hb.r5,
    (h 6 (by omega)).trans hb.r6, (h 7 (by omega)).trans hb.r7, (h 8 (by omega)).trans hb.r8,
    (h 9 (by omega)).trans hb.r9, (h 10 (by omega)).trans hb.r10,
    (h 11 (by omega)).trans hb.r11⟩

lemma RTRegs.mem {st : State} {n m tailArr headArr r outPtr sPtr : ℕ}
    (hb : RTRegs st n m tailArr headArr r outPtr sPtr) (mem' : ℕ → ℕ) :
    RTRegs { st with mem := mem' } n m tailArr headArr r outPtr sPtr :=
  ⟨hb.r0, hb.r1, hb.r2, hb.r3, hb.r4, hb.r5, hb.r6, hb.r7, hb.r8, hb.r9, hb.r10, hb.r11⟩

end

end MinCostFlow.LSF.Program
