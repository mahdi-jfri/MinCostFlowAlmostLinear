module

public import WordRAM.Logic
public import MinCostFlow.Expander.WordRAMHelpers
public import MinCostFlow.Expander.CsrBfsProg
public import MinCostFlow.Expander.ExpanderPruning

/-!
# Doubly-Linked Level Buckets and Layout Invariants for Pruning in WordRAM

Provides the shared register/memory layout (`PruneMemInv`, `PruneWordBound`, `PruneMemDisjoint`),
doubly-linked bucket invariant (`DoublyLinked`), `O(1)` link/unlink primitives (`unlinkLvlStmt`,
`linkLvlStmt`), and bucket sweep helper (`walkBucketStmt`) used by `PruningInitProg`,
`PruningStepsProg`, and `PruningProg`.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Register Map, Workspace Size, and Disjointness -/

abbrev prG : ℕ := 0
abbrev prCsr : ℕ := 1
abbrev prInB : ℕ := 2
abbrev prOutR : ℕ := 3
abbrev prWork : ℕ := 4
abbrev prCcap : ℕ := 5
abbrev prH : ℕ := 6
abbrev prTheta : ℕ := 7
abbrev prN : ℕ := 8
abbrev prM : ℕ := 9
abbrev prActTop : ℕ := 10
abbrev prPeelTop : ℕ := 11

abbrev prDegX : ℕ := 12
abbrev prHArr : ℕ := 13
abbrev prCur : ℕ := 14
abbrev prAbs : ℕ := 15
abbrev prEx : ℕ := 16
abbrev prDegR : ℕ := 17
abbrev prInAct : ℕ := 18
abbrev prActStk : ℕ := 19
abbrev prPeelStk : ℕ := 20
abbrev prLvlNext : ℕ := 21
abbrev prLvlPrev : ℕ := 22
abbrev prRemArr : ℕ := 23
abbrev prFlowEnc : ℕ := 24
abbrev prLvlVol : ℕ := 25
abbrev prLvlHead : ℕ := 26
abbrev prCsrAdjV : ℕ := 27
abbrev prCsrAdjH : ℕ := 28

abbrev prI : ℕ := 29
abbrev prJ : ℕ := 30
abbrev prU : ℕ := 31
abbrev prW : ℕ := 32
abbrev prIdx : ℕ := 33
abbrev prDir : ℕ := 34
abbrev prTmp1 : ℕ := 35
abbrev prTmp2 : ℕ := 36
abbrev prTmp3 : ℕ := 37
abbrev prRc : ℕ := 38
abbrev prDelta : ℕ := 39
abbrev prEnd : ℕ := 40
abbrev prStart : ℕ := 41
abbrev prSuf : ℕ := 42
abbrev prPicked : ℕ := 43

/-- Total scratch words required at `workAddr` for `n` vertices, `m` edges, height `H`. -/
def pruneWorkSpace (n m H : ℕ) : ℕ :=
  12 * n + m + 2 * H + 2

/-- Word-size bound ensuring every address and intermediate value fits in `< 2^w`. -/
def PruneWordBound (w n m C_cap H workAddr : ℕ) : Prop :=
  max (workAddr + pruneWorkSpace n m H + 2)
      (8 * C_cap * m + 4 * C_cap + 2 * n + 2 * m + H + 16) < 2 ^ w

lemma pruneWordBound_pos {w n m C_cap H workAddr : ℕ}
    (hw : PruneWordBound w n m C_cap H workAddr) :
    16 < 2 ^ w := by
  unfold PruneWordBound at hw
  omega

/-- Disjointness of input blocks (`gAddr`, `csrAddr`, `inBAddr`) from mutable arrays
(`outRAddr`, `workAddr`) and between `outRAddr` and `workAddr`. -/
def PruneMemDisjoint (gAddr csrAddr inBAddr outRAddr workAddr n m H lenG : ℕ) : Prop :=
  (outRAddr + n ≤ gAddr ∨ gAddr + lenG ≤ outRAddr) ∧
  (outRAddr + n ≤ csrAddr ∨ csrAddr + 2 * n + 1 + 4 * m ≤ outRAddr) ∧
  (outRAddr + n ≤ inBAddr ∨ inBAddr + n ≤ outRAddr) ∧
  (workAddr + pruneWorkSpace n m H ≤ gAddr ∨ gAddr + lenG ≤ workAddr) ∧
  (workAddr + pruneWorkSpace n m H ≤ csrAddr ∨ csrAddr + 2 * n + 1 + 4 * m ≤ workAddr) ∧
  (workAddr + pruneWorkSpace n m H ≤ inBAddr ∨ inBAddr + n ≤ workAddr) ∧
  (outRAddr + n ≤ workAddr ∨ workAddr + pruneWorkSpace n m H ≤ outRAddr)

abbrev wDegX (workAddr _n _m _H : ℕ) : ℕ := workAddr
abbrev wHArr (workAddr n _m _H : ℕ) : ℕ := workAddr + n
abbrev wCur (workAddr n _m _H : ℕ) : ℕ := workAddr + 2 * n
abbrev wAbs (workAddr n _m _H : ℕ) : ℕ := workAddr + 3 * n
abbrev wEx (workAddr n _m _H : ℕ) : ℕ := workAddr + 4 * n
abbrev wDegR (workAddr n _m _H : ℕ) : ℕ := workAddr + 5 * n
abbrev wInAct (workAddr n _m _H : ℕ) : ℕ := workAddr + 6 * n
abbrev wActStk (workAddr n _m _H : ℕ) : ℕ := workAddr + 7 * n
abbrev wPeelStk (workAddr n _m _H : ℕ) : ℕ := workAddr + 8 * n
abbrev wLvlNext (workAddr n _m _H : ℕ) : ℕ := workAddr + 9 * n
abbrev wLvlPrev (workAddr n _m _H : ℕ) : ℕ := workAddr + 10 * n
abbrev wRemArr (workAddr n _m _H : ℕ) : ℕ := workAddr + 11 * n
abbrev wFlowEnc (workAddr n _m _H : ℕ) : ℕ := workAddr + 12 * n
abbrev wLvlVol (workAddr n m _H : ℕ) : ℕ := workAddr + 12 * n + m
abbrev wLvlHead (workAddr n m H : ℕ) : ℕ := workAddr + 12 * n + m + H + 1

/-! ## 2. Doubly-Linked Level Buckets -/

/-- Inductive doubly-linked list invariant starting at `headVal` with sentinel `n` and
initial predecessor value `prevVal`. -/
def DoublyLinked (mem : ℕ → ℕ) (nextAddr prevAddr n : ℕ) : List ℕ → ℕ → ℕ → Prop
  | [], _, headVal => headVal = n
  | a :: as, prevVal, headVal =>
      headVal = a ∧ a < n ∧ mem (prevAddr + a) = prevVal ∧
        DoublyLinked mem nextAddr prevAddr n as a (mem (nextAddr + a))

lemma doublyLinked_mem_lt {mem : ℕ → ℕ} {nextAddr prevAddr n : ℕ} :
    ∀ {L : List ℕ} {prevVal headVal x : ℕ},
      DoublyLinked mem nextAddr prevAddr n L prevVal headVal → x ∈ L → x < n
  | _ :: _, _, _, _, hdl, hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hdl.2.1
      · exact doublyLinked_mem_lt hdl.2.2.2 hx'

lemma doublyLinked_congr_disjoint {mem₁ mem₂ : ℕ → ℕ} {nextAddr prevAddr n : ℕ}
    {L : List ℕ} {prevVal headVal : ℕ}
    (hnext : ∀ x ∈ L, mem₂ (nextAddr + x) = mem₁ (nextAddr + x))
    (hprev : ∀ x ∈ L, mem₂ (prevAddr + x) = mem₁ (prevAddr + x))
    (hdl : DoublyLinked mem₁ nextAddr prevAddr n L prevVal headVal) :
    DoublyLinked mem₂ nextAddr prevAddr n L prevVal headVal := by
  induction L generalizing prevVal headVal with
  | nil => exact hdl
  | cons a as ih =>
      rcases hdl with ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hprev a List.mem_cons_self, h3]
      · rw [hnext a List.mem_cons_self]
        exact ih (fun x hx => hnext x (List.mem_cons_of_mem _ hx))
          (fun x hx => hprev x (List.mem_cons_of_mem _ hx)) h4

lemma doublyLinked_push_front {mem mem' : ℕ → ℕ} {headAddr nextAddr prevAddr n x headVal : ℕ}
    {L : List ℕ}
    (hnd : L.Nodup) (hx : x < n) (hxNot : x ∉ L)
    (hdl : DoublyLinked mem nextAddr prevAddr n L n headVal)
    (hhead' : mem' headAddr = x)
    (hnextX : mem' (nextAddr + x) = headVal)
    (hprevX : mem' (prevAddr + x) = n)
    (hprevHead : ∀ h, headVal = h → h < n → mem' (prevAddr + h) = x)
    (hnextPres : ∀ y ∈ L, mem' (nextAddr + y) = mem (nextAddr + y))
    (hprevPres : ∀ y ∈ L, headVal ≠ y → mem' (prevAddr + y) = mem (prevAddr + y)) :
    DoublyLinked mem' nextAddr prevAddr n (x :: L) n (mem' headAddr) := by
  refine ⟨hhead', hx, hprevX, ?_⟩
  rw [hnextX]
  cases L with
  | nil => exact hdl
  | cons b bs =>
      rcases hdl with ⟨hb1, hb2, _, hb4⟩
      have hnd' := List.nodup_cons.mp hnd
      refine ⟨hb1, hb2, hprevHead b hb1 hb2, ?_⟩
      rw [hnextPres b List.mem_cons_self]
      apply doublyLinked_congr_disjoint
      · intro y hy; exact hnextPres y (List.mem_cons_of_mem _ hy)
      · intro y hy
        have hby : b ≠ y := fun heq => hnd'.1 (heq ▸ hy)
        exact hprevPres y (List.mem_cons_of_mem _ hy) (fun heq => hby (hb1.symm.trans heq))
      · exact hb4

lemma doublyLinked_append_split {mem : ℕ → ℕ} {nextAddr prevAddr n : ℕ} :
    ∀ (l1 l2 : List ℕ) (x pv hv : ℕ),
      DoublyLinked mem nextAddr prevAddr n (l1 ++ x :: l2) pv hv →
      x < n ∧
      (l1 = [] → hv = x ∧ mem (prevAddr + x) = pv) ∧
      (l1 ≠ [] → ∃ p, p ∈ l1 ∧ p < n ∧ mem (prevAddr + x) = p) ∧
      DoublyLinked mem nextAddr prevAddr n l2 x (mem (nextAddr + x))
  | [], l2, x, pv, hv, hdl => by
      simp only [List.nil_append] at hdl
      exact ⟨hdl.2.1, fun _ => ⟨hdl.1, hdl.2.2.1⟩, fun h => absurd rfl h, hdl.2.2.2⟩
  | a :: as, l2, x, pv, hv, hdl => by
      simp only [List.cons_append] at hdl
      rcases hdl with ⟨_, ha_lt, _, hrest⟩
      have ih := doublyLinked_append_split as l2 x a (mem (nextAddr + a)) hrest
      refine ⟨ih.1, fun h => absurd h (List.cons_ne_nil a as), fun _ => ?_, ih.2.2.2⟩
      cases as with
      | nil =>
          have h0 := ih.2.1 rfl
          exact ⟨a, List.mem_cons_self, ha_lt, h0.2⟩
      | cons c cs =>
          rcases ih.2.2.1 (List.cons_ne_nil c cs) with ⟨p, hp_mem, hp_lt, hprv⟩
          exact ⟨p, List.mem_cons_of_mem _ hp_mem, hp_lt, hprv⟩

private lemma doublyLinked_erase_core {mem mem' : ℕ → ℕ} {nextAddr prevAddr n : ℕ} :
    ∀ (l1 l2 : List ℕ) (x pv hv hv' : ℕ),
      (l1 ++ x :: l2).Nodup →
      DoublyLinked mem nextAddr prevAddr n (l1 ++ x :: l2) pv hv →
      (l1 = [] → hv' = mem (nextAddr + x)) →
      (l1 ≠ [] → hv' = hv) →
      (∀ y ∈ l1, mem' (nextAddr + y) =
        if y = mem (prevAddr + x) then mem (nextAddr + x) else mem (nextAddr + y)) →
      (∀ y ∈ l1, mem' (prevAddr + y) = mem (prevAddr + y)) →
      (∀ y ∈ l2, mem' (nextAddr + y) = mem (nextAddr + y)) →
      (∀ y ∈ l2, mem' (prevAddr + y) =
        if y = mem (nextAddr + x) then mem (prevAddr + x) else mem (prevAddr + y)) →
      DoublyLinked mem' nextAddr prevAddr n (l1 ++ l2) pv hv'
  | [], l2, x, pv, hv, hv', hnd, hdl, hhNil, _, _, _, hnext2, hprev2 => by
      simp only [List.nil_append] at hnd hdl ⊢
      have hnd2 : l2.Nodup := (List.nodup_cons.mp hnd).2
      rw [hhNil rfl]
      rcases hdl with ⟨_, _, hprvX, htail⟩
      cases l2 with
      | nil => exact htail
      | cons b bs =>
          rcases htail with ⟨hb1, hb2, _, hb4⟩
          have hb_nd : b ∉ bs := (List.nodup_cons.mp hnd2).1
          have hpb : mem' (prevAddr + b) = pv := by
            simp only [hprev2 b List.mem_cons_self, hb1, ↓reduceIte, hprvX]
          refine ⟨hb1, hb2, hpb, ?_⟩
          rw [hnext2 b List.mem_cons_self]
          apply doublyLinked_congr_disjoint
          · intro y hy; exact hnext2 y (List.mem_cons_of_mem _ hy)
          · intro y hy
            have hne : y ≠ mem (nextAddr + x) := fun heq => hb_nd (hb1 ▸ heq ▸ hy)
            simp only [hprev2 y (List.mem_cons_of_mem _ hy), hne, ↓reduceIte]
          · exact hb4
  | a :: as, l2, x, pv, hv, hv', hnd, hdl, _, hhCons, hnext1, hprev1, hnext2, hprev2 => by
      simp only [List.cons_append] at hnd hdl ⊢
      have hnd_a := List.nodup_cons.mp hnd
      rcases hdl with ⟨ha1, ha2, ha3, ha4⟩
      have hhv' : hv' = a := (hhCons (List.cons_ne_nil a as)).trans ha1
      have hprv_a : mem' (prevAddr + a) = pv :=
        (hprev1 a List.mem_cons_self).trans ha3
      refine ⟨hhv', ha2, hprv_a, ?_⟩
      apply doublyLinked_erase_core as l2 x a (mem (nextAddr + a)) (mem' (nextAddr + a))
        hnd_a.2 ha4
      · intro has
        subst has
        have hsplit := doublyLinked_append_split [] l2 x a (mem (nextAddr + a)) ha4
        have hprvX : mem (prevAddr + x) = a := (hsplit.2.1 rfl).2
        simp only [hnext1 a List.mem_cons_self, hprvX, ↓reduceIte]
      · intro has
        have hsplit := doublyLinked_append_split as l2 x a (mem (nextAddr + a)) ha4
        rcases hsplit.2.2.1 has with ⟨p, hp_mem, _, hprvX⟩
        have hap : a ≠ p := fun h => hnd_a.1 (List.mem_append_left _ (h ▸ hp_mem))
        simp only [hnext1 a List.mem_cons_self, hprvX, hap, ↓reduceIte]
      · intro y hy; exact hnext1 y (List.mem_cons_of_mem _ hy)
      · intro y hy; exact hprev1 y (List.mem_cons_of_mem _ hy)
      · exact hnext2
      · exact hprev2

private lemma list_erase_append_right_of_not_mem {x : ℕ} :
    ∀ {l1 l2 : List ℕ}, x ∉ l1 → (l1 ++ x :: l2).erase x = l1 ++ l2
  | [], l2, _ => by simp [List.erase_cons_head]
  | a :: as, l2, hnot => by
      have hax : a ≠ x := fun h => hnot (h ▸ List.mem_cons_self)
      have hbeq : (a == x) = false := beq_false_of_ne hax
      change (a :: (as ++ x :: l2)).erase x = a :: (as ++ l2)
      rw [List.erase_cons, hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      exact list_erase_append_right_of_not_mem (fun h => hnot (List.mem_cons_of_mem a h))

lemma doublyLinked_erase {mem mem' : ℕ → ℕ} {headAddr nextAddr prevAddr n x : ℕ}
    {L : List ℕ}
    (hnd : L.Nodup) (hx : x ∈ L)
    (hdl : DoublyLinked mem nextAddr prevAddr n L n (mem headAddr))
    (hhead' : mem' headAddr = if mem (prevAddr + x) = n then mem (nextAddr + x) else mem headAddr)
    (hnextPres : ∀ y ∈ L.erase x, mem' (nextAddr + y) =
      if y = mem (prevAddr + x) then mem (nextAddr + x) else mem (nextAddr + y))
    (hprevPres : ∀ y ∈ L.erase x, mem' (prevAddr + y) =
      if y = mem (nextAddr + x) then mem (prevAddr + x) else mem (prevAddr + y)) :
    DoublyLinked mem' nextAddr prevAddr n (L.erase x) n (mem' headAddr) := by
  rcases List.append_of_mem hx with ⟨l1, l2, rfl⟩
  have hx_not_l1 : x ∉ l1 := by
    have hnd1 := (List.nodup_append.mp hnd).2.2
    exact fun h => hnd1 x h x List.mem_cons_self rfl
  have herase : (l1 ++ x :: l2).erase x = l1 ++ l2 :=
    list_erase_append_right_of_not_mem hx_not_l1
  rw [herase]
  have hsplit := doublyLinked_append_split l1 l2 x n (mem headAddr) hdl
  apply doublyLinked_erase_core l1 l2 x n (mem headAddr) (mem' headAddr) hnd hdl
  · intro hl1
    have h0 := (hsplit.2.1 hl1).2
    simp only [hhead', h0, ↓reduceIte]
  · intro hl1
    rcases hsplit.2.2.1 hl1 with ⟨p, _, hp_lt, hp_eq⟩
    have hne : mem (prevAddr + x) ≠ n := by rw [hp_eq]; omega
    simp only [hhead', hne, ↓reduceIte]
  · intro y hy
    exact hnextPres y (herase ▸ List.mem_append_left _ hy)
  · intro y hy
    have hy2 : y ∈ l1 ++ l2 := List.mem_append_left _ hy
    have hne : y ≠ mem (nextAddr + x) := by
      intro heq
      cases l2 with
      | nil =>
          have hnx : mem (nextAddr + x) = n := hsplit.2.2.2
          have hylt : y < n := doublyLinked_mem_lt hdl (List.mem_append_left _ hy)
          omega
      | cons b bs =>
          have hnx : mem (nextAddr + x) = b := hsplit.2.2.2.1
          have hmem_b : b ∈ x :: b :: bs := List.mem_cons_of_mem x List.mem_cons_self
          have hyb : y = b := heq.trans hnx
          exact (List.nodup_append.mp hnd).2.2 y hy b hmem_b hyb
    simp only [hprevPres y (herase ▸ hy2), hne, ↓reduceIte]
  · intro y hy
    have hne : y ≠ mem (prevAddr + x) := by
      intro heq
      cases l1 with
      | nil =>
          have hpx : mem (prevAddr + x) = n := (hsplit.2.1 rfl).2
          have hylt : y < n := doublyLinked_mem_lt hdl (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
          omega
      | cons c cs =>
          rcases hsplit.2.2.1 (List.cons_ne_nil c cs) with ⟨p, hp_mem, _, hpx⟩
          have hmem_y : y ∈ x :: l2 := List.mem_cons_of_mem x hy
          exact (List.nodup_append.mp hnd).2.2 p hp_mem y hmem_y (hpx.symm.trans heq.symm)
    simp only [hnextPres y (herase ▸ List.mem_append_right _ hy), hne, ↓reduceIte]
  · intro y hy
    exact hprevPres y (herase ▸ List.mem_append_right _ hy)

/-! ## 3. Shared WordRAM State Invariant -/

structure PruneMemInv (cfg : PruneCfg) (gAddr csrAddr inBAddr outRAddr workAddr : ℕ)
    (s : PruneState) (buckets : ℕ → List ℕ) (st : State) : Prop where
  cfg_X : cfg.X = Finset.range cfg.G.n
  cfg_valid : cfg.Valid
  reg_g : st.regs prG = gAddr
  reg_csr : st.regs prCsr = csrAddr
  reg_inB : st.regs prInB = inBAddr
  reg_outR : st.regs prOutR = outRAddr
  reg_work : st.regs prWork = workAddr
  reg_ccap : st.regs prCcap = cfg.C_cap
  reg_H : st.regs prH = cfg.H
  reg_theta : st.regs prTheta = cfg.θ_out_nat
  reg_n : st.regs prN = cfg.G.n
  reg_m : st.regs prM = cfg.G.m
  reg_actTop : st.regs prActTop = s.active.length
  reg_peelTop : st.regs prPeelTop = s.peelQ.length
  reg_degX : st.regs prDegX = wDegX workAddr cfg.G.n cfg.G.m cfg.H
  reg_hArr : st.regs prHArr = wHArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_cur : st.regs prCur = wCur workAddr cfg.G.n cfg.G.m cfg.H
  reg_abs : st.regs prAbs = wAbs workAddr cfg.G.n cfg.G.m cfg.H
  reg_ex : st.regs prEx = wEx workAddr cfg.G.n cfg.G.m cfg.H
  reg_degR : st.regs prDegR = wDegR workAddr cfg.G.n cfg.G.m cfg.H
  reg_inAct : st.regs prInAct = wInAct workAddr cfg.G.n cfg.G.m cfg.H
  reg_actStk : st.regs prActStk = wActStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_peelStk : st.regs prPeelStk = wPeelStk workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlNext : st.regs prLvlNext = wLvlNext workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlPrev : st.regs prLvlPrev = wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H
  reg_remArr : st.regs prRemArr = wRemArr workAddr cfg.G.n cfg.G.m cfg.H
  reg_flowEnc : st.regs prFlowEnc = wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlVol : st.regs prLvlVol = wLvlVol workAddr cfg.G.n cfg.G.m cfg.H
  reg_lvlHead : st.regs prLvlHead = wLvlHead workAddr cfg.G.n cfg.G.m cfg.H
  reg_adjV : st.regs prCsrAdjV = csrAddr + 2 * cfg.G.n + 1
  reg_adjH : st.regs prCsrAdjH = csrAddr + 2 * cfg.G.n + 1 + 2 * cfg.G.m
  graph_at : GraphAt st.mem gAddr cfg.G
  csr_at : HasCsrAt st.mem csrAddr cfg.G
  inB_eq : ∀ b, b ∈ cfg.B ↔ b < cfg.G.n ∧ st.mem (inBAddr + b) ≠ 0
  outR_eq : ∀ u < cfg.G.n, st.mem (outRAddr + u) = if s.inR u then 1 else 0
  degX_eq : ∀ u < cfg.G.n, st.mem (wDegX workAddr cfg.G.n cfg.G.m cfg.H + u) = cfg.degX u
  h_eq : ∀ u < cfg.G.n, st.mem (wHArr workAddr cfg.G.n cfg.G.m cfg.H + u) = s.h u
  cur_eq : ∀ u < cfg.G.n, st.mem (wCur workAddr cfg.G.n cfg.G.m cfg.H + u) = s.cur u
  abs_eq : ∀ u < cfg.G.n, st.mem (wAbs workAddr cfg.G.n cfg.G.m cfg.H + u) = s.abs u
  ex_eq : ∀ u < cfg.G.n, st.mem (wEx workAddr cfg.G.n cfg.G.m cfg.H + u) = s.ex u
  degR_eq : ∀ u < cfg.G.n, st.mem (wDegR workAddr cfg.G.n cfg.G.m cfg.H + u) = s.degR u
  inAct_eq : ∀ u < cfg.G.n,
    st.mem (wInAct workAddr cfg.G.n cfg.G.m cfg.H + u) = if s.inActive u then 1 else 0
  actStk_eq : ∀ i < s.active.length,
    st.mem (wActStk workAddr cfg.G.n cfg.G.m cfg.H + i) = s.active.getD (s.active.length - 1 - i) 0
  peelStk_eq : ∀ i < s.peelQ.length,
    st.mem (wPeelStk workAddr cfg.G.n cfg.G.m cfg.H + i) = s.peelQ.getD (s.peelQ.length - 1 - i) 0
  flowEnc_eq : ∀ idx < cfg.G.m,
    st.mem (wFlowEnc workAddr cfg.G.n cfg.G.m cfg.H + idx) = (↑cfg.C_cap + s.flow idx).toNat
  lvlVol_H : st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + cfg.H) = 0
  lvlVol_eq : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
    st.mem (wLvlVol workAddr cfg.G.n cfg.G.m cfg.H + ℓ) = volAtLevel cfg s.inR s.h ℓ
  buckets_nodup : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H → (buckets ℓ).Nodup
  buckets_mem : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
    ∀ x, x ∈ buckets ℓ ↔ x < cfg.G.n ∧ s.inR x = true ∧ s.h x = ℓ
  buckets_dl : ∀ ℓ, 1 ≤ ℓ → ℓ < cfg.H →
    DoublyLinked st.mem (wLvlNext workAddr cfg.G.n cfg.G.m cfg.H)
      (wLvlPrev workAddr cfg.G.n cfg.G.m cfg.H) cfg.G.n
      (buckets ℓ) cfg.G.n (st.mem (wLvlHead workAddr cfg.G.n cfg.G.m cfg.H + ℓ))
  ex_bound : ∀ u < cfg.G.n, s.ex u ≤ 4 * cfg.C_cap * cfg.G.m
  prune_inv : PruningInv cfg s
  peelQ_inv : PeelQInv cfg s

private lemma incEdgesAux_eq_csrIncAux (u k : ℕ) :
    ∀ L : List (ℕ × ℕ), incEdgesAux u k L = csrIncAux u k L
  | [] => rfl
  | (a, b) :: rest => by
      dsimp only [incEdgesAux, csrIncAux]
      have ih := incEdgesAux_eq_csrIncAux u (k + 1) rest
      by_cases hab : a = b
      · simp [hab, ih]
      · simp only [hab, ↓reduceIte]
        by_cases hau : a = u
        · simp [hau, ih]
        · by_cases hbu : b = u
          · simp [hau, hbu, ih]
          · simp [hau, hbu, ih]

lemma PruneMemInv.cfg_edges {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) :
    cfg.edges = cfg.G.edges := by
  unfold PruneCfg.edges
  have hx : cfg.X = cfg.G.verts := h.cfg_X
  rw [hx, inside_verts_of_isValid h.cfg_valid.1]

lemma PruneMemInv.cfg_incEdges {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) (u : ℕ) :
    cfg.incEdges u = csrIncAux u 0 cfg.G.edges := by
  unfold PruneCfg.incEdges
  rw [h.cfg_edges]
  exact incEdgesAux_eq_csrIncAux u 0 cfg.G.edges

lemma PruneMemInv.active_len_le {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) :
    s.active.length ≤ cfg.G.n := by
  have hsub : s.active.toFinset ⊆ Finset.range cfg.G.n := fun x hx =>
    h.cfg_X ▸ h.prune_inv.active_sub x (List.mem_toFinset.mp hx)
  calc
    s.active.length = s.active.toFinset.card := (List.toFinset_card_of_nodup h.prune_inv.active_nodup).symm
    _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card hsub
    _ = cfg.G.n := Finset.card_range _

lemma PruneMemInv.peelQ_len_le {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) :
    s.peelQ.length ≤ cfg.G.n := by
  have hpq : s.peelQ.Nodup ∧ (∀ x ∈ s.peelQ, x ∈ cfg.X) ∧
      (∀ x ∈ s.peelQ, s.degR x < cfg.θ_out_nat) := h.peelQ_inv
  have hsub : s.peelQ.toFinset ⊆ Finset.range cfg.G.n := fun x hx =>
    h.cfg_X ▸ hpq.2.1 x (List.mem_toFinset.mp hx)
  calc
    s.peelQ.length = s.peelQ.toFinset.card := (List.toFinset_card_of_nodup hpq.1).symm
    _ ≤ (Finset.range cfg.G.n).card := Finset.card_le_card hsub
    _ = cfg.G.n := Finset.card_range _

lemma PruneMemInv.degX_eq_graph_deg {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) (u : ℕ) :
    cfg.degX u = cfg.G.deg u := by
  unfold PruneCfg.degX Graph.deg Graph.verts
  rw [h.cfg_X]

lemma PruneMemInv.sum_degX_eq_two_mul_m {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) :
    (∑ u ∈ Finset.range cfg.G.n, cfg.degX u) = 2 * cfg.G.m := by
  have hsum := sum_deg_eq_two_mul_m h.cfg_valid.1
  change (∑ u ∈ Finset.range cfg.G.n, cfg.G.deg u) = 2 * cfg.G.m at hsum
  simpa only [h.degX_eq_graph_deg] using hsum

lemma PruneMemInv.degX_le_two_mul_m {cfg : PruneCfg} {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) {u : ℕ} (hu : u < cfg.G.n) :
    cfg.degX u ≤ 2 * cfg.G.m := by
  have hle : cfg.degX u ≤ ∑ x ∈ Finset.range cfg.G.n, cfg.degX x :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hu)
  have hsum := h.sum_degX_eq_two_mul_m
  omega

lemma PruneMemInv.volAtLevel_le_two_mul_m {cfg : PruneCfg}
    {gAddr csrAddr inBAddr outRAddr workAddr : ℕ}
    {s : PruneState} {buckets : ℕ → List ℕ} {st : State}
    (h : PruneMemInv cfg gAddr csrAddr inBAddr outRAddr workAddr s buckets st) (ℓ : ℕ) :
    volAtLevel cfg s.inR s.h ℓ ≤ 2 * cfg.G.m := by
  unfold volAtLevel
  rw [h.cfg_X]
  calc
    ∑ u ∈ Finset.range cfg.G.n, (if (s.inR u && decide (s.h u = ℓ)) = true then cfg.degX u else 0)
      ≤ ∑ u ∈ Finset.range cfg.G.n, cfg.degX u := by
        apply Finset.sum_le_sum
        intro u _
        split_ifs <;> omega
    _ = 2 * cfg.G.m := h.sum_degX_eq_two_mul_m

private lemma edgeContrib_le_two_mul_cap (inR : ℕ → Bool) (flow : ℕ → ℤ) (C_cap : ℕ)
    (p : ℕ × Bool × ℕ) (hcap : -↑C_cap ≤ flow p.1 ∧ flow p.1 ≤ ↑C_cap) :
    edgeContrib inR flow C_cap p ≤ 2 * (C_cap : ℤ) := by
  cases hr : inR p.2.2 <;> cases hd : p.2.1 <;>
    simp [edgeContrib, flowDir, hr, hd] <;> omega

lemma ex_le_bound_of_inR {cfg : PruneCfg} {s : PruneState}
    (hcfgX : cfg.X = Finset.range cfg.G.n) (hval : cfg.Valid) (hinv : PruningInv cfg s)
    {u : ℕ} (huR : s.inR u = true) :
    s.ex u ≤ 4 * cfg.C_cap * cfg.G.m := by
  have hfb := hinv.flow_balance u huR
  have hsum_le : (List.map (edgeContrib s.inR s.flow cfg.C_cap) (cfg.incEdges u)).sum ≤
      (cfg.incEdges u).length * (2 * (cfg.C_cap : ℤ)) := by
    have haux : ∀ L : List (ℕ × Bool × ℕ),
        (∀ q ∈ L, q.1 < cfg.edges.length) →
        (List.map (edgeContrib s.inR s.flow cfg.C_cap) L).sum ≤ L.length * (2 * (cfg.C_cap : ℤ)) := by
      intro L
      induction L with
      | nil => intro _; simp
      | cons q qs ih =>
          intro hqL
          have hq : edgeContrib s.inR s.flow cfg.C_cap q ≤ 2 * (cfg.C_cap : ℤ) :=
            edgeContrib_le_two_mul_cap s.inR s.flow cfg.C_cap q
              (hinv.flow_cap q.1 (hqL q List.mem_cons_self))
          have hqs := ih (fun r hr => hqL r (List.mem_cons_of_mem q hr))
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          push_cast
          linarith
    apply haux
    intro q hq
    have hbd := incEdgesAux_idx_ge (u := u) (k := 0) (L := cfg.edges) hq
    simpa only [Nat.zero_add] using hbd.2
  have huX : u ∈ cfg.X := hinv.inR_sub u huR
  rw [hcfgX, Finset.mem_range] at huX
  have hsum_deg : (∑ x ∈ Finset.range cfg.G.n, cfg.degX x) = 2 * cfg.G.m := by
    have hdx : ∀ x, cfg.degX x = cfg.G.deg x := fun x => by
      unfold PruneCfg.degX Graph.deg Graph.verts; rw [hcfgX]
    have hsum := sum_deg_eq_two_mul_m hval.1
    change (∑ x ∈ Finset.range cfg.G.n, cfg.G.deg x) = 2 * cfg.G.m at hsum
    simpa only [hdx] using hsum
  have hdeg_le : cfg.degX u ≤ 2 * cfg.G.m := by
    have h1 := Finset.single_le_sum (f := cfg.degX) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr huX)
    omega
  have hlen : (cfg.incEdges u).length ≤ 2 * cfg.G.m :=
    le_trans (incEdges_length_le_degX cfg u) hdeg_le
  have hZ : (s.ex u : ℤ) ≤ 4 * (cfg.C_cap : ℤ) * (cfg.G.m : ℤ) := by
    have hmul : (cfg.incEdges u).length * (2 * cfg.C_cap) ≤ 2 * cfg.G.m * (2 * cfg.C_cap) :=
      Nat.mul_le_mul_right _ hlen
    have hmulZ : ((cfg.incEdges u).length : ℤ) * (2 * (cfg.C_cap : ℤ)) ≤
        4 * (cfg.C_cap : ℤ) * (cfg.G.m : ℤ) := by
      have : ((cfg.incEdges u).length * (2 * cfg.C_cap) : ℤ) ≤
          (2 * cfg.G.m * (2 * cfg.C_cap) : ℤ) := by exact_mod_cast hmul
      linarith
    linarith
  exact_mod_cast hZ

/-! ## 4. Unlink, Link, and Walk Bucket Primitives -/

/-- Unlinks vertex in `prU` from its current level bucket `ℓ = h[prU]` (`1 ≤ ℓ < H`). -/
def unlinkLvlStmt : Stmt :=
  seqStmts [
    .assign prTmp2 (.load (.bin .add (.reg prHArr) (.reg prU))),
    .assign prTmp1 (.bin .add (.reg prLvlVol) (.reg prTmp2)),
    .assign prTmp3 (.load (.reg prTmp1)),
    .assign prSuf (.load (.bin .add (.reg prDegX) (.reg prU))),
    .store (.reg prTmp1) (.bin .sub (.reg prTmp3) (.reg prSuf)),
    .assign prTmp3 (.load (.bin .add (.reg prLvlPrev) (.reg prU))),
    .assign prSuf (.load (.bin .add (.reg prLvlNext) (.reg prU))),
    .cond (.bin .eq (.reg prTmp3) (.reg prN))
      (.store (.bin .add (.reg prLvlHead) (.reg prTmp2)) (.reg prSuf))
      (.store (.bin .add (.reg prLvlNext) (.reg prTmp3)) (.reg prSuf)),
    .cond (.bin .lt (.reg prSuf) (.reg prN))
      (.store (.bin .add (.reg prLvlPrev) (.reg prSuf)) (.reg prTmp3))
      .nop
  ]

lemma unlinkLvlStmt_noRand : unlinkLvlStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Stmt.NoRand]

/-- Links vertex in `prU` onto the front of bucket `ℓ = prTmp2` (`1 ≤ ℓ < H`). -/
def linkLvlStmt : Stmt :=
  seqStmts [
    .assign prTmp1 (.bin .add (.reg prLvlHead) (.reg prTmp2)),
    .assign prSuf (.load (.reg prTmp1)),
    .store (.bin .add (.reg prLvlNext) (.reg prU)) (.reg prSuf),
    .store (.bin .add (.reg prLvlPrev) (.reg prU)) (.reg prN),
    .cond (.bin .lt (.reg prSuf) (.reg prN))
      (.store (.bin .add (.reg prLvlPrev) (.reg prSuf)) (.reg prU))
      .nop,
    .store (.reg prTmp1) (.reg prU),
    .assign prTmp1 (.bin .add (.reg prLvlVol) (.reg prTmp2)),
    .assign prTmp3 (.load (.reg prTmp1)),
    .assign prSuf (.load (.bin .add (.reg prDegX) (.reg prU))),
    .store (.reg prTmp1) (.bin .add (.reg prTmp3) (.reg prSuf))
  ]

lemma linkLvlStmt_noRand : linkLvlStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Stmt.NoRand]

/-- Sweeps bucket `prStart = ℓ` appending all its vertices into `remArr` starting at `prEnd`,
then clears `lvlVol[ℓ] := 0` and `lvlHead[ℓ] := n`. -/
def walkBucketStmt : Stmt :=
  seqStmts [
    .assign prU (.load (.bin .add (.reg prLvlHead) (.reg prStart))),
    .loop (.bin .lt (.reg prU) (.reg prN))
      (seqStmts [
        .store (.bin .add (.reg prRemArr) (.reg prEnd)) (.reg prU),
        .assign prEnd (.bin .add (.reg prEnd) (.const 1)),
        .assign prU (.load (.bin .add (.reg prLvlNext) (.reg prU)))
      ]),
    .store (.bin .add (.reg prLvlVol) (.reg prStart)) (.const 0),
    .store (.bin .add (.reg prLvlHead) (.reg prStart)) (.reg prN)
  ]

lemma walkBucketStmt_noRand : walkBucketStmt.NoRand := by
  apply seqStmts_noRand
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]
  · simp [Stmt.NoRand]

/-! ## 5. Triples for Unlink, Link, and WalkBucket -/

lemma eval_reg {w : ℕ} {st : State} {r val : ℕ}
    (hr : st.regs r = val) (_hlt : val < 2 ^ w) :
    Expr.eval w st (.reg r) = some val := by
  simp only [Expr.eval, hr]

lemma eval_add_regs {w : ℕ} {st : State} {r₁ r₂ v₁ v₂ : ℕ}
    (h1 : st.regs r₁ = v₁) (h2 : st.regs r₂ = v₂) (hlt : v₁ + v₂ < 2 ^ w) :
    Expr.eval w st (.bin .add (.reg r₁) (.reg r₂)) = some (v₁ + v₂) := by
  simp only [Expr.eval, h1, h2, WordRAM.BinOp.eval, hlt, ↓reduceIte]

lemma eval_load_add_regs {w : ℕ} {st : State} {r₁ r₂ v₁ v₂ val : ℕ}
    (h1 : st.regs r₁ = v₁) (h2 : st.regs r₂ = v₂) (hadd : v₁ + v₂ < 2 ^ w)
    (hm : st.mem (v₁ + v₂) = val) (_hval : val < 2 ^ w) :
    Expr.eval w st (.load (.bin .add (.reg r₁) (.reg r₂))) = some val := by
  rw [Expr.eval, eval_add_regs h1 h2 hadd]
  simp only [Option.map_some, hm]

lemma doublyLinked_split_vals {mem : ℕ → ℕ} {headAddr nextAddr prevAddr n x : ℕ}
    {L : List ℕ} (hx : x ∈ L) (hdl : DoublyLinked mem nextAddr prevAddr n L n (mem headAddr)) :
    (mem (prevAddr + x) = n ∨ mem (prevAddr + x) < n) ∧
    (mem (nextAddr + x) = n ∨ mem (nextAddr + x) < n) := by
  rcases List.append_of_mem hx with ⟨l1, l2, rfl⟩
  have hs := doublyLinked_append_split l1 l2 x n (mem headAddr) hdl
  refine ⟨?_, ?_⟩
  · cases l1 with
    | nil => exact Or.inl (hs.2.1 rfl).2
    | cons a as =>
        rcases hs.2.2.1 (List.cons_ne_nil a as) with ⟨p, _, hp, hpeq⟩
        exact Or.inr (hpeq ▸ hp)
  · cases l2 with
    | nil => exact Or.inl hs.2.2.2
    | cons b bs =>
        exact Or.inr (hs.2.2.2.1 ▸ hs.2.2.2.2.1)

lemma memFrame_update_in {m : ℕ → ℕ} {addr v lo hi : ℕ}
    (hlo : lo ≤ addr) (hhi : addr < hi) :
    MemFrame m (Function.update m addr v) lo hi := fun k hk => by
  have hne : k ≠ addr := by rcases hk with h | h <;> omega
  exact Function.update_of_ne hne v m

/-- Memory-preservation summary for bucket pointer/volume updates at level `ℓ`. -/
def BucketMemPreserved (mem mem' : ℕ → ℕ) (workAddr n m H ℓ : ℕ) : Prop :=
  MemFrame mem mem' (wLvlNext workAddr n m H) (wLvlHead workAddr n m H + H + 1) ∧
  (∀ k, wLvlPrev workAddr n m H + n ≤ k → k < wLvlVol workAddr n m H → mem' k = mem k) ∧
  (∀ ℓ', ℓ' ≤ H → ℓ' ≠ ℓ →
    mem' (wLvlVol workAddr n m H + ℓ') = mem (wLvlVol workAddr n m H + ℓ') ∧
    mem' (wLvlHead workAddr n m H + ℓ') = mem (wLvlHead workAddr n m H + ℓ'))

lemma bucketMemPreserved_refl (mem : ℕ → ℕ) (workAddr n m H ℓ : ℕ) :
    BucketMemPreserved mem mem workAddr n m H ℓ :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

lemma bucketMemPreserved_trans {m1 m2 m3 : ℕ → ℕ} {workAddr n m H ℓ : ℕ}
    (h12 : BucketMemPreserved m1 m2 workAddr n m H ℓ)
    (h23 : BucketMemPreserved m2 m3 workAddr n m H ℓ) :
    BucketMemPreserved m1 m3 workAddr n m H ℓ :=
  ⟨memFrame_trans h12.1 h23.1,
    fun k hk1 hk2 => (h23.2.1 k hk1 hk2).trans (h12.2.1 k hk1 hk2),
    fun ℓ' h1 h2 => ⟨(h23.2.2 ℓ' h1 h2).1.trans (h12.2.2 ℓ' h1 h2).1,
      (h23.2.2 ℓ' h1 h2).2.trans (h12.2.2 ℓ' h1 h2).2⟩⟩


end MinCostFlow.Expander
