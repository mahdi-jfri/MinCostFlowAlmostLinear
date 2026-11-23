module

public import MinCostFlow.SparseCore.Program.AssemblyFirstInitSlotFront
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# The slots of the active pairs at the init: the run (`AssemblyFirstInitSlotRun`)

This file proves that `slotListBody` runs and says what it leaves (`slotList_runs`). The front
(the setup and loops 1 to 3) is `slotListFront_runs`. The tail (`slotListTail_runs`) runs loop 4,
the sort of the keys and the removal of repeats, the two header words, and loops 5 and 6.

An edge `e` is *selected* (`slotSel`) when it is not a forest edge of P4's export and the flag of
its component is on. Its key is `c · B` plus its bucket word, where `c` is its component
(`slotKeyOf`). The result (`SlotListOut`) names two lists: `S`, the selected edges in the order of
the edge list of `G`, and `D`, their keys in increasing order without repeats. The slot of a key is
its index in `D`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner.Program

/-- An edge is selected: it is not a forest edge, and the flag of its component is on. -/
noncomputable def slotSel (mem : ℕ → ℕ) (cmpH : ℕ) (G : MGraph) (fe : List ℕ) (k e : ℕ) :
    Bool :=
  decide (e ∉ fe ∧ SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) (slotCOf mem cmpH G e)))

/-- The key of an edge: its component times `B`, plus its bucket word. -/
def slotKeyOf (mem : ℕ → ℕ) (cmpH bktH B : ℕ) (G : MGraph) (e : ℕ) : ℕ :=
  slotCOf mem cmpH G e * B + mem (bktH + e)

theorem slot_key_lt {c x B n : ℕ} (hc : c < n) (hx : x < B) : c * B + x < n * B := by
  calc c * B + x < c * B + B := by omega
    _ = (c + 1) * B := by ring
    _ ≤ n * B := Nat.mul_le_mul_right B hc

/-- The cost of the tail of the procedure. -/
def slotTailCost (m : ℕ) : ℕ := 250 * (m * (Nat.log 2 (m + 1) + 1)) + 400 * m + 200

theorem slotTail_cost_le {m s d : ℕ} (hs : s ≤ m) (hd : d ≤ s) :
    m * 110 + 200 * s * (Nat.log 2 (s + 1) + 1) + 45 * s + d * 120 +
      s * (45 * (Nat.log 2 (d + 1) + 1) + 80) + 150 ≤ slotTailCost m := by
  have l1 : Nat.log 2 (s + 1) ≤ Nat.log 2 (m + 1) := Nat.log_mono_right (by omega)
  have l2 : Nat.log 2 (d + 1) ≤ Nat.log 2 (m + 1) := Nat.log_mono_right (by omega)
  have h1 : s * (Nat.log 2 (s + 1) + 1) ≤ m * (Nat.log 2 (m + 1) + 1) :=
    Nat.mul_le_mul hs (by omega)
  have h2 : s * (45 * (Nat.log 2 (d + 1) + 1) + 80) ≤ m * (45 * (Nat.log 2 (m + 1) + 1) + 80) :=
    Nat.mul_le_mul hs (by omega)
  have h3 : m * (45 * (Nat.log 2 (m + 1) + 1) + 80) =
      45 * (m * (Nat.log 2 (m + 1) + 1)) + 80 * m := by ring
  have h4 : 200 * s * (Nat.log 2 (s + 1) + 1) = 200 * (s * (Nat.log 2 (s + 1) + 1)) := by ring
  unfold slotTailCost
  omega

/-- **What the procedure leaves.** `S` lists the selected edges without repeats, and `D` their keys
in increasing order without repeats. With `m = G.m`, `pairs = heap + 2 + eCap + 3 m`,
`slots = heap + 2 + eCap + 5 m`, `specs = heap + 3 + eCap + 6 m` and
`asg = heap + 3 + eCap + 8 m`:
* the header words at `heap` and `heap + 1` hold `|D|` and `|S|`;
* the word `ctH + 3 c` holds the flag of component `c`, the word `ctH + 3 c + 2` the length of the
  segment of `c` in `D`, and the word `ctH + 3 c + 1` the address of its pairs;
* the pair `j` is `(D[j] mod B, j)`, the slot list is `0, 1, …, |D| - 1`, the spec `s` is
  `(s, 4 · (number of selected edges with slot s))`, and the assignment `t` is
  `(S[t], slot of S[t])`;
* the memory below `ctH` and between the table of the components and `heap` is as before, and the
  memory from the end is zero. -/
structure SlotListOut (mem mem' : ℕ → ℕ) (G : MGraph) (fe : List ℕ)
    (cmpH bktH nComp k B ctH heap eCap : ℕ) (S D : List ℕ) : Prop where
  S_nodup : S.Nodup
  S_mem : ∀ e, e ∈ S ↔ e ∈ G.E ∧ slotSel mem cmpH G fe k e = true
  S_len : S.length ≤ G.m
  D_sorted : D.Pairwise (· < ·)
  D_mem : ∀ x, x ∈ D ↔ ∃ e ∈ S, slotKeyOf mem cmpH bktH B G e = x
  D_len : D.length ≤ S.length
  nD : mem' heap = D.length
  nK : mem' (heap + 1) = S.length
  flag : ∀ c < nComp, mem' (ctH + 3 * c) =
    if SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) c) then 1 else 0
  ptr : ∀ c < nComp, mem' (ctH + 3 * c + 1) =
    if 0 < slotSegLen D B c then heap + 2 + eCap + 3 * G.m + 2 * slotSegStart D B c else 0
  len : ∀ c < nComp, mem' (ctH + 3 * c + 2) = slotSegLen D B c
  pairs : ∀ j (hj : j < D.length), mem' (heap + 2 + eCap + 3 * G.m + 2 * j) = D[j] % B ∧
    mem' (heap + 2 + eCap + 3 * G.m + 2 * j + 1) = j
  slots : ∀ j < D.length, mem' (heap + 2 + eCap + 5 * G.m + j) = j
  specs : ∀ s < D.length, mem' (heap + 3 + eCap + 6 * G.m + 2 * s) = s ∧
    mem' (heap + 3 + eCap + 6 * G.m + 2 * s + 1) =
      4 * (S.filter fun e => D.idxOf (slotKeyOf mem cmpH bktH B G e) = s).length
  asg : ∀ t (ht : t < S.length), mem' (heap + 3 + eCap + 8 * G.m + 2 * t) = S[t] ∧
    mem' (heap + 3 + eCap + 8 * G.m + 2 * t + 1) = D.idxOf (slotKeyOf mem cmpH bktH B G S[t])
  low : ∀ a < ctH, mem' a = mem a
  mid : ∀ a, ctH + 3 * nComp ≤ a → a < heap → mem' a = mem a
  zero : ZeroFrom mem' (heap + slotListSpace eCap G.m)

/-- The facts that loop 4 needs on one edge, from the memory after the front. -/
theorem slotKeyEdge_of_front {w : ℕ} {mem memF : ℕ → ℕ} {graph cmpH bktH nComp k B ctH heap vCap
    eCap : ℕ} {G : MGraph} {fe : List ℕ} {e : ℕ}
    (helt : e < eCap)
    (a1 : graph + 4 + 7 * vCap + 3 * eCap + e < ctH)
    (a2 : graph + 4 + 4 * vCap + mem (graph + 4 + 7 * vCap + 3 * eCap + e) < ctH)
    (a3 : mem (graph + 4 + 4 * vCap + mem (graph + 4 + 7 * vCap + 3 * eCap + e)) = G.tail e)
    (hcmp : cmpH + G.tail e < ctH ∧ slotCOf mem cmpH G e < nComp)
    (hbkt : bktH + e < ctH ∧ mem (bktH + e) < B)
    (hct : ctH + 3 * nComp ≤ heap) (hkw : nComp * B < 2 ^ w)
    (hlow : ∀ a, a < ctH → memF a = mem a)
    (hF2 : ∀ c < nComp, memF (ctH + 3 * c) =
      if SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) c) then 1 else 0)
    (hF3 : memF (heap + 2 + e) = if e ∈ fe then 1 else 0) :
    SlotKeyEdge w memF (graph + 4 + 7 * vCap + 3 * eCap) (graph + 4 + 4 * vCap) cmpH bktH ctH
      (heap + 2) (heap + 2 + eCap) B (slotCOf mem cmpH G) (slotKeyOf mem cmpH bktH B G)
      (slotSel mem cmpH G fe k) e := by
  obtain ⟨c1, c2⟩ := hcmp
  obtain ⟨b1, b2⟩ := hbkt
  have m1 : memF (graph + 4 + 7 * vCap + 3 * eCap + e) =
      mem (graph + 4 + 7 * vCap + 3 * eCap + e) := hlow _ a1
  have m2 : memF (graph + 4 + 4 * vCap + mem (graph + 4 + 7 * vCap + 3 * eCap + e)) = G.tail e := by
    rw [hlow _ a2, a3]
  have m3 : memF (cmpH + G.tail e) = slotCOf mem cmpH G e := hlow _ c1
  have m4 : memF (bktH + e) = mem (bktH + e) := hlow _ b1
  have hflag := hF2 _ c2
  refine ⟨by omega, by rw [m1]; omega, by rw [m1, m2]; omega, by rw [m1, m2, m3], by omega,
    by omega, by omega, by rw [hflag]; split_ifs <;> omega, ?_, fun _ => ⟨by rw [m4]; rfl, ?_⟩⟩
  · rw [hF3, hflag]
    unfold slotSel
    rw [decide_eq_true_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [ite_eq_right h1], by rw [ite_eq_left h2]; omega⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h => ?_, ?_⟩
      · rw [ite_eq_left h] at h1
        omega
      · by_contra h
        rw [ite_eq_right h] at h2
        exact h2 rfl
  · have := slot_key_lt c2 b2
    unfold slotKeyOf
    omega

set_option maxHeartbeats 1000000 in
/-- **The tail of `slotListBody`**: loop 4, the sort and the removal of repeats, the header, loops
5 and 6, and the return. It starts from the state that the front leaves
(`slotListFront_runs`). -/
theorem slotListTail_runs {w b : ℕ} {p : Program} (hpSort : p.HasAt (b + 1) (sortProcs (b + 1)))
    {ω : ℕ → Bool} {graph cmpH bktH nComp k B ctH heap vCap eCap nF fTrip : ℕ} {G : MGraph}
    {mem : ℕ → ℕ} {st : State}
    (hG : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ ctH)
    (hcmp : ∀ e ∈ G.E, cmpH + G.tail e < ctH ∧ slotCOf mem cmpH G e < nComp)
    (hbkt : ∀ e ∈ G.E, bktH + e < ctH ∧ mem (bktH + e) < B)
    (hct : ctH + 3 * nComp ≤ heap) (hz : ZeroFrom mem ctH)
    (hw : heap + slotListSpace eCap G.m + 4 * G.m + 4 < 2 ^ w) (hkw : nComp * B < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w)
    (hR : SlotRegs st.regs graph cmpH bktH nComp k B ctH heap vCap eCap G.m nF fTrip)
    (hF1 : ∀ a, ¬ SlotCtCell ctH nComp a → (a < heap + 2 ∨ heap + 2 + eCap ≤ a) →
      st.mem a = mem a)
    (hF2 : ∀ c < nComp, st.mem (ctH + 3 * c) =
      if SlotFlagOn k (slotCnt G (slotCOf mem cmpH G) c) then 1 else 0)
    (hF3 : ∀ e < eCap, st.mem (heap + 2 + e) =
      if e ∈ slotForestEdges mem fTrip nF then 1 else 0) :
    ∃ o st' c, Runs w p ω (slotListTail (b + 1)) st o st' c ∧
      (o = .returned (heap + slotListSpace eCap G.m) ∧
        ∃ S D, SlotListOut mem st'.mem G (slotForestEdges mem fTrip nF) cmpH bktH nComp k B ctH
          heap eCap S D) ∧
      c ≤ slotTailCost G.m := by
  obtain ⟨hGval, hVlt, hElt, -, -, -, -, -, -, hext, -, -,
    ⟨eL, heLen, heNd, heMem, heLA, -⟩, hslot, -⟩ := hG
  obtain ⟨r2, r3, -, -, r6, r7, r8, r11, r12, r13, r14, -, -, r17, r18, r19, r20, r21, r22, r23,
    r24⟩ := hR
  have hsz : graph + (4 + 7 * vCap + 9 * eCap) ≤ ctH := hGle
  have hsp : heap + (eCap + 10 * G.m + 3) + 4 * G.m + 4 < 2 ^ w := hw
  have hmE : G.m ≤ eCap := by
    unfold MGraph.m
    calc G.E.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hElt e he)
      _ = eCap := Finset.card_range eCap
  have hlow : ∀ a, a < ctH → st.mem a = mem a := fun a ha =>
    hF1 a (fun ⟨c, _, h⟩ => by omega) (Or.inl (by omega))
  have heLA' : ListAt st.mem (graph + 4 + 7 * vCap + eCap) eL :=
    heLA.congr fun a _ h2 => hlow a (by rw [heLen] at h2; simp only [dgEListBase] at h2; omega)
  have hE4 : ∀ e ∈ eL, SlotKeyEdge w st.mem (graph + 4 + 7 * vCap + 3 * eCap)
      (graph + 4 + 4 * vCap) cmpH bktH ctH (heap + 2) (heap + 2 + eCap) B (slotCOf mem cmpH G)
      (slotKeyOf mem cmpH bktH B G) (slotSel mem cmpH G (slotForestEdges mem fTrip nF) k) e := by
    intro e he
    have heE : e ∈ G.E := (heMem e).mp he
    have helt := hElt e heE
    have htV : G.tail e ∈ G.V := (hGval e heE).1
    obtain ⟨hsV, hback⟩ := hext _ htV
    have hts : mem (graph + 4 + 7 * vCap + 3 * eCap + e) =
        mem (graph + 4 + 3 * vCap + G.tail e) := (hslot e heE).1
    have hsV' : mem (graph + 4 + 3 * vCap + G.tail e) < vCap := hVlt _ hsV
    exact slotKeyEdge_of_front helt (by omega) (by rw [hts]; omega) (by rw [hts]; exact hback)
      (hcmp e heE) (hbkt e heE) hct hkw hlow hF2 (hF3 e helt)
  refine runs_start_le ?_
  unfold slotListTail
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  -- loop 4
  refine runs_seq_triple_le (slotKey_loop (w := w) (p := p) (mem := st.mem) (eL := eL)
    (eLB := graph + 4 + 7 * vCap + eCap) (tsB := graph + 4 + 7 * vCap + 3 * eCap)
    (iteB := graph + 4 + 4 * vCap) (cmpH := cmpH) (bktH := bktH) (ctH := ctH)
    (markH := heap + 2) (keysH := heap + 2 + eCap) (asgH := heap + 3 + eCap + 8 * G.m) (B := B)
    (slotCOf mem cmpH G) (slotKeyOf mem cmpH bktH B G)
    (slotSel mem cmpH G (slotForestEdges mem fTrip nF) k) st.regs heLA' (by omega) hE4
    (by omega) (by omega) hw16 r2 r3 r6 r7 (r11.trans heLen.symm) r12 r13 r14 r17 r18 r24)
    ⟨rfl, by simp, fun r hr => by simp [show r ≠ 29 by omega]⟩ (fun st₄ h₄ => ?_)
  obtain ⟨hR4, h29, hfr4, hkeys4, hasg4⟩ := h₄
  obtain ⟨S, hS⟩ : ∃ S, S = eL.filter (slotSel mem cmpH G (slotForestEdges mem fTrip nF) k) :=
    ⟨_, rfl⟩
  rw [← hS] at h29 hkeys4 hasg4
  have hSlen : S.length ≤ G.m := by rw [hS, ← heLen]; exact List.length_filter_le _ _
  have hSmem : ∀ e, e ∈ S ↔ e ∈ G.E ∧ slotSel mem cmpH G (slotForestEdges mem fTrip nF) k e =
      true := fun e => by rw [hS, List.mem_filter, heMem]
  have hkeyw : ∀ x ∈ S.map (slotKeyOf mem cmpH bktH B G), x < 2 ^ w := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨heE, hsel⟩ := (hSmem e).mp he
    exact ((hE4 e ((heMem e).mpr heE)).2.2.2.2.2.2.2.2.2 hsel).2
  have q18 : st₄.regs 18 = heap + 2 + eCap := (hR4 18 (by omega)).trans r18
  have q19 : st₄.regs 19 = heap + 2 + eCap + G.m := (hR4 19 (by omega)).trans r19
  have q20 : st₄.regs 20 = heap + 2 + eCap + 2 * G.m := (hR4 20 (by omega)).trans r20
  -- the sort
  have hms := mergeSort_meetsContract (w := w) (p := p) (b := b + 1) (bSort := b + 1)
    (L := S.map (slotKeyOf mem cmpH bktH B G)) hpSort hpSort
  refine runs_seq_call_le hms
    (vs := [heap + 2 + eCap, (S.map (slotKeyOf mem cmpH bktH B G)).length, heap + 2 + eCap + G.m])
    (by rw [List.length_map]; eval_expr) (by intro v hv; simp at hv; omega)
    ⟨_, _, rfl, hw16, by simp; omega, by simp; omega, Or.inl (by simp; omega), hkeys4, hkeyw⟩
    (fun v mem' pos' hpost => ?_)
  obtain ⟨a, scr, L', hargs, -, hperm, hsorted, hlist', hfr'⟩ := hpost
  simp only [List.cons.injEq, and_true, true_and] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  have hlen' : L'.length = S.length := by rw [hperm.length_eq, List.length_map]
  have hL'w : ∀ x ∈ L', x < 2 ^ w := fun x hx => hkeyw x (hperm.subset hx)
  -- the removal of repeats
  have hdd := dedup_meetsContract (w := w) (p := p) (b := b + 1) (bSort := b + 1) (L := L') hpSort
  have q18' : Function.update st₄.regs 30 v 18 = heap + 2 + eCap := by simp [q18]
  have q29' : Function.update st₄.regs 30 v 29 = S.length := by simp [h29]
  have q20' : Function.update st₄.regs 30 v 20 = heap + 2 + eCap + 2 * G.m := by simp [q20]
  refine runs_seq_call_le hdd (vs := [heap + 2 + eCap, L'.length, heap + 2 + eCap + 2 * G.m])
    (by rw [hlen']; eval_expr) (by intro v hv; simp at hv; omega)
    ⟨_, _, rfl, hw16, by omega, by omega, Or.inl (by omega), hsorted, hlist', hL'w⟩
    (fun v' mem'' pos'' hpost' => ?_)
  obtain ⟨src, dst, hargs', hret, hlt, hmemD, hlist'', hfr''⟩ := hpost'
  simp only [List.cons.injEq, and_true, true_and] at hargs'
  obtain ⟨rfl, rfl⟩ := hargs'
  obtain ⟨D, hD⟩ : ∃ D, D = sortedDedup L' := ⟨_, rfl⟩
  rw [← hD] at hret hlt hmemD hlist'' hfr''
  have hDnd : D.Nodup := hlt.imp fun h => Nat.ne_of_lt h
  have hDlen : D.length ≤ S.length := by
    rw [← hlen']
    exact (hDnd.subperm fun x hx => (hmemD x).mp hx).length_le
  have hDmem : ∀ x, x ∈ D ↔ ∃ e ∈ S, slotKeyOf mem cmpH bktH B G e = x := fun x => by
    rw [hmemD, hperm.mem_iff, List.mem_map]
  -- the registers from here on
  have hv' : v' = D.length := hret
  let R5 : ℕ → ℕ := Function.update (Function.update st₄.regs 30 v) 30 v'
  have hR5 : ∀ r, r < 25 → R5 r = st.regs r := fun r hr => by
    simp only [R5]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hR4 r (Or.inl hr)
  have s6 : R5 6 = B := (hR5 6 (by norm_num)).trans r6
  have s7 : R5 7 = ctH := (hR5 7 (by norm_num)).trans r7
  have s8 : R5 8 = heap := (hR5 8 (by norm_num)).trans r8
  have s11 : R5 11 = G.m := (hR5 11 (by norm_num)).trans r11
  have s20 : R5 20 = heap + 2 + eCap + 2 * G.m := (hR5 20 (by norm_num)).trans r20
  have s21 : R5 21 = heap + 2 + eCap + 3 * G.m := (hR5 21 (by norm_num)).trans r21
  have s22 : R5 22 = heap + 2 + eCap + 5 * G.m := (hR5 22 (by norm_num)).trans r22
  have s23 : R5 23 = heap + 3 + eCap + 6 * G.m := (hR5 23 (by norm_num)).trans r23
  have s24 : R5 24 = heap + 3 + eCap + 8 * G.m := (hR5 24 (by norm_num)).trans r24
  have s29 : R5 29 = S.length := by
    simp only [R5]
    rw [Function.update_of_ne (by norm_num), Function.update_of_ne (by norm_num), h29]
  have s30 : R5 30 = D.length := by simp only [R5, Function.update_self, hv']
  clear hR5 hR4 r2 r3 r6 r7 r8 r11 r12 r13 r14 r17 r18 r19 r20 r21 r22 r23 r24 q18 q19 q20 q18'
    q29' q20' h29 hret hv' hE4 heLA' hkeyw hlow
  -- the header
  refine runs_seq_store_le (x := heap) (v := D.length) (Expr.eval_reg_of_eq s8)
    (Expr.eval_reg_of_eq s30) ?_
  refine runs_seq_store_le (x := heap + 1) (v := S.length)
    (Expr.eval_add (Expr.eval_reg_of_eq s8) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq s29) ?_
  -- the memory before loop 5, back to `st`
  let M5 : ℕ → ℕ := Function.update (Function.update mem'' heap D.length) (heap + 1) S.length
  have hM5 : ∀ a, a ≠ heap → a ≠ heap + 1 →
      (a < heap + 2 + eCap + 2 * G.m ∨ heap + 2 + eCap + 2 * G.m + D.length ≤ a) →
      (a < heap + 2 + eCap ∨ heap + 2 + eCap + S.length ≤ a) →
      (a < heap + 2 + eCap + G.m ∨ heap + 2 + eCap + G.m + S.length ≤ a) → M5 a = st₄.mem a :=
    fun a h1 h2 h3 h4 h5 => by
      simp only [M5]
      rw [Function.update_of_ne h2, Function.update_of_ne h1, hfr'' a h3]
      exact hfr' a (by simpa using h4) (by simpa using h5)
  have hM5st : ∀ a, a ≠ heap → a ≠ heap + 1 → (a < heap + 2 + eCap ∨
      heap + 2 + eCap + 2 * G.m + D.length ≤ a ∧ a < heap + 3 + eCap + 8 * G.m ∨
      heap + 3 + eCap + 10 * G.m ≤ a) → M5 a = st.mem a := fun a h1 h2 h3 => by
    rw [hM5 a h1 h2 (by omega) (by omega) (by omega)]
    exact hfr4 a (by omega) (by omega)
  have hM5mem : ∀ a, ctH ≤ a → ¬ SlotCtCell ctH nComp a → a ≠ heap → a ≠ heap + 1 →
      (a < heap + 2 ∨ heap + 2 + eCap + 2 * G.m + D.length ≤ a ∧
        a < heap + 3 + eCap + 8 * G.m ∨ heap + 3 + eCap + 10 * G.m ≤ a) → M5 a = 0 :=
    fun a h0 hn h1 h2 h3 => by
      rw [hM5st a h1 h2 (by omega), hF1 a hn (by omega)]
      exact hz a h0
  have hDA5 : ListAt M5 (heap + 2 + eCap + 2 * G.m) D :=
    (hlist''.update_outside (Or.inl (by omega))).update_outside (Or.inl (by omega))
  have hDw : ∀ x ∈ D, x < 2 ^ w := fun x hx => hL'w x ((hmemD x).mp hx)
  have hDc : ∀ x ∈ D, x / B < nComp := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := (hDmem x).mp hx
    obtain ⟨heE, -⟩ := (hSmem e).mp he
    unfold slotKeyOf
    rw [key_div (hbkt e heE).2]
    exact (hcmp e heE).2
  have hz5 : ∀ c < nComp, M5 (ctH + 3 * c + 1) = 0 ∧ M5 (ctH + 3 * c + 2) = 0 := fun c hc =>
    ⟨hM5mem _ (by omega) (fun ⟨c', _, h⟩ => by omega) (by omega) (by omega) (Or.inl (by omega)),
      hM5mem _ (by omega) (fun ⟨c', _, h⟩ => by omega) (by omega) (by omega) (Or.inl (by omega))⟩
  -- loop 5
  refine runs_seq_triple_le (slotWalk_loop (w := w) (p := p) (mem := M5) (D := D)
    (DH := heap + 2 + eCap + 2 * G.m) (ctH := ctH) (pairsH := heap + 2 + eCap + 3 * G.m)
    (slotsH := heap + 2 + eCap + 5 * G.m) (specsH := heap + 3 + eCap + 6 * G.m) (nComp := nComp)
    (B := B) R5 hlt hDA5 hDw hDc hz5 (by omega) (by omega) (by omega) (by omega) (by omega) hw16
    s6 s7 s20 s21 s22 s23 s30) ⟨rfl, fun r _ => rfl⟩ (fun st₅ h₅ => ?_)
  obtain ⟨hR5', hfr5, hdone5, hct5⟩ := h₅
  -- loop 6
  have hwalk : ∀ a, (a < ctH ∨ ctH + 3 * nComp ≤ a ∧ a < heap + 2 + eCap + 3 * G.m ∨
      heap + 3 + eCap + 8 * G.m ≤ a) →
      ¬ SlotWalkCell ctH nComp (heap + 2 + eCap + 3 * G.m) (heap + 2 + eCap + 5 * G.m)
        (heap + 3 + eCap + 6 * G.m) D.length a := by
    rintro a ha (⟨c, hc, h | h⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨j, hj, h⟩) <;> omega
  have hDA6 : ListAt st₅.mem (heap + 2 + eCap + 2 * G.m) D :=
    hDA5.congr fun a h1 h2 => hfr5 a (hwalk a (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  have hasg6 : ∀ t (ht : t < S.length), st₅.mem (heap + 3 + eCap + 8 * G.m + 2 * t + 1) =
      slotKeyOf mem cmpH bktH B G S[t] := fun t ht => by
    rw [hfr5 (heap + 3 + eCap + 8 * G.m + 2 * t + 1) (hwalk _ (Or.inr (Or.inr (by omega)))),
      hM5 (heap + 3 + eCap + 8 * G.m + 2 * t + 1) (by omega) (by omega) (by omega) (by omega)
        (by omega)]
    exact (hasg4 t ht).2
  have hspec6 : ∀ s < D.length, st₅.mem (heap + 3 + eCap + 6 * G.m + 2 * s + 1) = 0 := by
    intro s hs
    rw [hfr5 (heap + 3 + eCap + 6 * G.m + 2 * s + 1) (by
      rintro (⟨c, hc, h | h⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨j, hj, h⟩) <;> omega)]
    exact hM5mem _ (by omega) (fun ⟨c', _, h⟩ => by omega) (by omega) (by omega)
      (Or.inr (Or.inl ⟨by omega, by omega⟩))
  have hkeyD : ∀ e ∈ S, slotKeyOf mem cmpH bktH B G e ∈ D := fun e he =>
    (hDmem _).mpr ⟨e, he, rfl⟩
  refine runs_seq_triple_le (slotAssign_loop (w := w) (p := p) (mem := st₅.mem) (D := D) (S := S)
    (DH := heap + 2 + eCap + 2 * G.m) (specsH := heap + 3 + eCap + 6 * G.m)
    (asgH := heap + 3 + eCap + 8 * G.m) (bSort := b + 1) (slotKeyOf mem cmpH bktH B G) R5 hpSort
    hlt hDA6 hDw hkeyD hasg6 hspec6 (by omega) (by omega) (by omega) hw16 s20 s23 s24 s29 s30)
    ⟨rfl, hR5'⟩ (fun st₆ h₆ => ?_)
  obtain ⟨hR6, hfr6, hasg6', hspec6'⟩ := h₆
  have t11 : st₆.regs 11 = G.m := (hR6 11 (by omega)).trans s11
  have t24 : st₆.regs 24 = heap + 3 + eCap + 8 * G.m := (hR6 24 (by omega)).trans s24
  -- back from `st₆` to `M5`
  have back6 : ∀ a, ¬ SlotAssignCell (heap + 3 + eCap + 6 * G.m) D.length
      (heap + 3 + eCap + 8 * G.m) S.length a →
      ¬ SlotWalkCell ctH nComp (heap + 2 + eCap + 3 * G.m) (heap + 2 + eCap + 5 * G.m)
        (heap + 3 + eCap + 6 * G.m) D.length a → st₆.mem a = M5 a := fun a h1 h2 => by
    rw [hfr6 a h1, hfr5 a h2]
  have nA : ∀ a, (a < heap + 3 + eCap + 6 * G.m ∨
      heap + 3 + eCap + 10 * G.m ≤ a) → ¬ SlotAssignCell (heap + 3 + eCap + 6 * G.m) D.length
        (heap + 3 + eCap + 8 * G.m) S.length a := by
    rintro a ha (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> omega
  have nW : ∀ a, (a < ctH ∨ ctH + 3 * nComp ≤ a ∧ a < heap + 2 + eCap + 3 * G.m ∨
      heap + 3 + eCap + 8 * G.m ≤ a) → ¬ SlotWalkCell ctH nComp (heap + 2 + eCap + 3 * G.m)
        (heap + 2 + eCap + 5 * G.m) (heap + 3 + eCap + 6 * G.m) D.length a := hwalk
  refine runs_ret_le (v := heap + slotListSpace eCap G.m)
    (Expr.eval_eq_of_eq (v₁ := heap + 3 + eCap + 8 * G.m + 2 * G.m)
      (Expr.eval_add (Expr.eval_reg_of_eq t24) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq t11) (by omega)) (by omega)) (by unfold slotListSpace; omega))
    ⟨rfl, S, D, ?_⟩ ?_
  · refine ⟨hS ▸ heNd.filter _, hSmem, hSlen, hlt, hDmem, hDlen, ?_, ?_, fun c hc => ?_,
      fun c hc => ?_, fun c hc => ?_, fun j hj => ?_, fun j hj => ?_, fun s hs => ?_,
      fun t ht => ?_, fun a ha => ?_, fun a ha1 ha2 => ?_, fun a ha => ?_⟩
    · -- the header
      rw [back6 heap (nA _ (Or.inl (by omega))) (nW _ (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
      simp only [M5]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [back6 (heap + 1) (nA _ (Or.inl (by omega)))
        (nW _ (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
      simp only [M5]
      rw [Function.update_self]
    · -- the flags
      rw [back6 (ctH + 3 * c) (nA _ (Or.inl (by omega))) (by
          rintro (⟨c', _, h | h⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨j, _, h⟩) <;> omega),
        hM5st (ctH + 3 * c) (by omega) (by omega) (Or.inl (by omega))]
      exact hF2 c hc
    · rw [hfr6 (ctH + 3 * c + 1) (nA _ (Or.inl (by omega)))]
      exact (hct5 c hc).1
    · rw [hfr6 (ctH + 3 * c + 2) (nA _ (Or.inl (by omega)))]
      exact (hct5 c hc).2
    · rw [hfr6 (heap + 2 + eCap + 3 * G.m + 2 * j) (nA _ (Or.inl (by omega))),
        hfr6 (heap + 2 + eCap + 3 * G.m + 2 * j + 1) (nA _ (Or.inl (by omega)))]
      exact ⟨(hdone5 j hj).1, (hdone5 j hj).2.1⟩
    · rw [hfr6 (heap + 2 + eCap + 5 * G.m + j) (nA _ (Or.inl (by omega)))]
      exact (hdone5 j hj).2.2.1
    · refine ⟨?_, hspec6' s hs⟩
      rw [hfr6 (heap + 3 + eCap + 6 * G.m + 2 * s)
        (by rintro (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> omega)]
      exact (hdone5 s hs).2.2.2
    · refine ⟨?_, hasg6' t ht⟩
      rw [hfr6 (heap + 3 + eCap + 8 * G.m + 2 * t)
          (by rintro (⟨s', hs', h⟩ | ⟨t', ht', h⟩) <;> omega),
        hfr5 (heap + 3 + eCap + 8 * G.m + 2 * t) (nW _ (Or.inr (Or.inr (by omega)))),
        hM5 (heap + 3 + eCap + 8 * G.m + 2 * t) (by omega) (by omega) (by omega) (by omega)
          (by omega)]
      exact (hasg4 t ht).1
    · -- the memory below `ctH`
      rw [back6 a (nA _ (Or.inl (by omega))) (nW _ (Or.inl ha)),
        hM5st a (by omega) (by omega) (Or.inl (by omega))]
      exact hF1 a (fun ⟨c, _, h⟩ => by omega) (Or.inl (by omega))
    · rw [back6 a (nA _ (Or.inl (by omega))) (nW _ (Or.inr (Or.inl ⟨ha1, by omega⟩))),
        hM5st a (by omega) (by omega) (Or.inl (by omega))]
      exact hF1 a (fun ⟨c, _, h⟩ => by omega) (Or.inl (by omega))
    · -- the memory from the end
      have ha' : heap + 3 + eCap + 10 * G.m ≤ a := by unfold slotListSpace at ha; omega
      rw [back6 a (nA _ (Or.inr ha')) (nW _ (Or.inr (Or.inr (by omega))))]
      exact hM5mem a (by omega) (fun ⟨c, _, h⟩ => by omega) (by omega) (by omega)
        (Or.inr (Or.inr ha'))
  · -- the cost
    have hc := slotTail_cost_le hSlen hDlen
    simp only [mergeSortContract, dedupContract, argsSize_cons, argsSize_nil, Expr.size_reg,
      Expr.size_const, Expr.size_bin, List.length_map]
    rw [hlen', heLen]
    omega

/-! ## The whole procedure -/

/-- The cost of `slotListBody`. -/
def slotListCost (m nComp nF : ℕ) : ℕ := slotFrontCost m nComp nF + slotTailCost m

/-- **The slot lists at the init.** Called as `[graph, expPtr, cmpH, bktH, nComp, k, B, ctH, heap]`
on the graph `G` at `graph`, P4's export at `expPtr` (with the forest edges as the first words of
the `nF` triples at `fTrip`), the components of the tails at `cmpH`, the bucket words at `bktH`
(below `B`), and zero memory from `ctH`, the procedure returns the end
`heap + slotListSpace eCap G.m` of its arrays and leaves `SlotListOut`. -/
theorem slotList_runs {w b : ℕ} {p : Program} (hp : p.HasAt b (slotListModule b)) (ω : ℕ → Bool)
    {pos graph expPtr cmpH bktH nComp k B ctH heap vCap eCap fD nF fTrip : ℕ} {G : MGraph}
    {mem : ℕ → ℕ}
    (hG : DynGraphAt mem graph vCap eCap G) (hGle : graph + dynGraphSize vCap eCap ≤ ctH)
    (hexp : mem (expPtr + 1) = fD) (hnF : mem (fD + 2) = nF) (hfT : mem (fD + 3) = fTrip)
    (hfe : ∀ e ∈ slotForestEdges mem fTrip nF, e ∈ G.E) (hfeL : fTrip + 3 * nF ≤ ctH)
    (hcmp : ∀ e ∈ G.E, cmpH + G.tail e < ctH ∧ slotCOf mem cmpH G e < nComp)
    (hbkt : ∀ e ∈ G.E, bktH + e < ctH ∧ mem (bktH + e) < B)
    (hct : ctH + 3 * nComp ≤ heap) (hz : ZeroFrom mem ctH)
    (hw : heap + slotListSpace eCap G.m + 4 * G.m + 4 < 2 ^ w) (hkw : nComp * B < 2 ^ w)
    (hw16 : 16 ≤ 2 ^ w) (hexpw : expPtr + 1 < 2 ^ w) (hfDw : fD + 3 < 2 ^ w) :
    ∃ o st' c, Runs w p ω (slotListBody (b + 1))
        (startState [graph, expPtr, cmpH, bktH, nComp, k, B, ctH, heap] mem pos) o st' c ∧
      (o = .returned (heap + slotListSpace eCap G.m) ∧
        ∃ S D, SlotListOut mem st'.mem G (slotForestEdges mem fTrip nF) cmpH bktH nComp k B ctH
          heap eCap S D) ∧
      c ≤ slotListCost G.m nComp nF := by
  have hpSort : p.HasAt (b + 1) (sortProcs (b + 1)) := by
    intro i hi
    have h := hp (i + 1) (by simp only [slotListModule, List.length_cons]; omega)
    rw [show b + 1 + i = b + (i + 1) by omega]
    simpa only [slotListModule, List.getElem_cons_succ] using h
  refine runs_start_le ?_
  unfold slotListBody
  refine slotListFront_runs hG hGle hexp hnF hfT hfe hfeL hcmp hct hz (by omega) hw16 hexpw hfDw
    (fun st hR hF1 hF2 hF3 => ?_)
  obtain ⟨o, st', c, hr, hq, hc⟩ :=
    slotListTail_runs (ω := ω) hpSort hG hGle hcmp hbkt hct hz hw hkw hw16 hR hF1 hF2 hF3
  exact ⟨o, st', c, hr, hq, by unfold slotListCost; omega⟩

end MinCostFlow.SparseCore.Program
