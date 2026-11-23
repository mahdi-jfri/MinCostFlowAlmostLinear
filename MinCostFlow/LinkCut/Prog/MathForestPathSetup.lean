module

public import MinCostFlow.LinkCut.Prog.MathForestFindRoot

/-!
# Shared Path-Query Setup (`reroot` + `expose` and Disjoint Copy Helpers)

Provides `SafeMem.ptr_disjoint_ans`, `evalMemSteps_root_unique`, `mem_of_exposeInvs`,
and `rerootExpose_runs` shared across `pathSum`, `pathMin`, `pathAdd`, and `cut`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num MinCostFlow.Rounding

section PathSetupHelpers

/-- Amortized constant factor for `lctPathSumBody` (`≤ 310000 * (L + 1) * (log(n+2)+1)`). -/
def C_PATHSUM_OP (L : ℕ) : ℕ := 310000 * (L + 1)

/-- Amortized constant factor for `lctPathMinBody` (`≤ 350000 * (L + 1) * (log(n+2)+1)`). -/
def C_PATHMIN_OP (L : ℕ) : ℕ := 350000 * (L + 1)

theorem evalMemSteps_nodeId_mem (mem : ℕ → ℕ) (nb h L : ℕ) :
    ∀ (t : AuxTree) (b : Bool) (δ : ℤ) (s : RawStep),
      s ∈ evalMemSteps mem nb h L t b δ → s.nodeId ∈ t.toList
  | .leaf, _, _, s, hs => by simp [evalMemSteps] at hs
  | .node x l r, b, δ, s, hs => by
      rw [evalMemSteps.eq_def] at hs
      dsimp only at hs
      set own := (Option.map (fun q => RawStep.addDeltaMod h L (if b = true then q.flip else q) δ)
        (nodeOwnRawStep mem nb h L x)).toList
      have hmem_own : ∀ q ∈ own, q.nodeId = x := by
        intro q hq
        dsimp only [own] at hq
        rw [Option.mem_toList] at hq
        rcases Option.mem_map.mp hq with ⟨orig, horig, rfl⟩
        unfold nodeOwnRawStep at horig
        split_ifs at horig with h0
        · simp at horig
        · obtain rfl := Option.some.inj horig
          cases b <;> unfold RawStep.addDeltaMod <;> split_ifs <;> rfl
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton]
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte, List.mem_append] at hs
        rcases hs with (hs' | hs') | hs'
        · exact Or.inr (evalMemSteps_nodeId_mem mem nb h L r _ _ s hs')
        · exact Or.inl (Or.inr (hmem_own s hs'))
        · exact Or.inl (Or.inl (evalMemSteps_nodeId_mem mem nb h L l _ _ s hs'))
      · have hbf : b = false := Bool.eq_false_iff.2 hb
        subst hbf
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append] at hs
        rcases hs with (hs' | hs') | hs'
        · exact Or.inl (Or.inl (evalMemSteps_nodeId_mem mem nb h L l _ _ s hs'))
        · exact Or.inl (Or.inr (hmem_own s hs'))
        · exact Or.inr (evalMemSteps_nodeId_mem mem nb h L r _ _ s hs')

theorem rawStep_addDeltaMod_zero {h L : ℕ} {orig : RawStep}
    (hf : Fits h L orig.flow) (haf : Fits h L orig.availFwd) (hab : Fits h L orig.availBwd) :
    orig.addDeltaMod h L 0 = orig := by
  rcases orig with ⟨nid, eid, eu, ev, fwd, cost, flow, af, ab⟩
  cases fwd <;> simp_all [RawStep.addDeltaMod, wrap_of_fits]

theorem evalMemSteps_root_unique {w h L cap p pp : ℕ} {mem : ℕ → ℕ} {nb : ℕ}
    {t : AuxTree} (ht : TreeMemMatch w h L mem nb cap t p pp)
    (hnd : t.toList.Nodup) (hne : t ≠ .leaf)
    (hrev : revFlag mem nb t.rootId = false)
    (hht : nodeField mem nb t.rootId OFF_HAS_TAG = 0)
    {s : RawStep} (hs : s ∈ evalMemSteps mem nb h L t false 0)
    (hs_id : s.nodeId = t.rootId) :
    nodeOwnRawStep mem nb h L t.rootId = some s := by
  cases t with
  | leaf => exact absurd rfl hne
  | node r l r' =>
      dsimp only [AuxTree.rootId] at hrev hht hs_id ⊢
      rw [evalMemSteps.eq_def] at hs
      dsimp only [AuxTree.toList] at hnd
      have hnd_top := List.nodup_append.mp hnd
      have hnd_left := List.nodup_append.mp hnd_top.1
      have hr_nl : r ∉ l.toList := fun hm =>
        hnd_left.2.2 r hm r (List.mem_singleton.2 rfl) rfl
      have hr_nr : r ∉ r'.toList := fun hm =>
        hnd_top.2.2 r (List.mem_append_right _ (List.mem_singleton.2 rfl)) r hm rfl
      have htag0 : nodeTagInt mem nb h L r = 0 := by simp [nodeTagInt, hht]
      dsimp only at hs
      simp [hrev, htag0] at hs
      rcases hs with hs' | hs' | hs'
      · exact absurd (hs_id ▸ evalMemSteps_nodeId_mem mem nb h L l false 0 s hs') hr_nl
      · rcases hs' with ⟨orig, horig, rfl⟩
        have hfits := ht.nodeOwn_fits r (by simp [AuxTree.toList]) orig horig
        rw [rawStep_addDeltaMod_zero hfits.1 hfits.2.1 hfits.2.2]
        exact horig
      · exact absurd (hs_id ▸ evalMemSteps_nodeId_mem mem nb h L r' false 0 s hs') hr_nr

theorem SafeMem.ptr_disjoint_ans {L b hp_caller ansLen : ℕ} {x₀ : LctConc}
    {mem₁ st_mem : ℕ → ℕ}
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hpf : PtrFootOk b mem₁ x₀ L)
    (hsafe : SafeMem mem₁ (lctNodesBase b) (lctCap x₀.n) (hp_caller + ansLen) st_mem)
    {x off : ℕ} (hx1 : 1 ≤ x) (hx2 : x ≤ lctCap x₀.n) (hoff : off ∈ ptrOffs) :
    let p := nodeField st_mem (lctNodesBase b) x off
    p = 0 ∨ hp_caller + ansLen ≤ p ∨ p + L ≤ hp_caller := by
  dsimp only
  have hpa := hsafe.2.2.2 x off hx1 hx2 hoff
  rcases hpa with hp0 | hp_hi | ⟨y, off', hy1, hy2, hoff', hy_eq⟩
  · exact Or.inl hp0
  · exact Or.inr (Or.inl hp_hi)
  · by_cases hpz : nodeField st_mem (lctNodesBase b) x off = 0
    · exact Or.inl hpz
    · have hpy := hpf y hy2 off' hoff'
      rw [← hy_eq] at hpy
      rcases hpy with h0 | ⟨_, _, hft⟩
      · exact Or.inl h0
      · refine Or.inr (Or.inr ?_)
        by_cases hL : L = 0
        · subst hL
          have h1 := hfoot _ (hft _ le_rfl (by omega))
          omega
        · have h1 := hfoot _ (hft (nodeField st_mem (lctNodesBase b) x off + (L - 1))
            (by omega) (by omega))
          omega

theorem mem_of_exposeInvs {w h L P b hp_caller hp_eff : ℕ} {F : MathForest} {x₀ : LctConc}
    {mem₀ mem₁ mem_end : ℕ → ℕ} {trees1 : List AuxTree}
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hhp_ge : hp_caller ≤ hp_eff)
    (hz0_safe : SlotZeroOk mem₁ (lctNodesBase b))
    (hpf0 : PtrFootOk b mem₁ x₀ L)
    (hag0 : ∀ a, a < b ∨ lctArenaHi b (lctCap F.n) ≤ a ∧ a < hp_caller → mem₁ a = mem₀ a)
    (hsafe : SafeMem mem₁ (lctNodesBase b) (lctCap F.n) hp_eff mem_end)
    (hi : LctExposeInvs w h L P b F.n x₀.freeEdges x₀.edgeMap trees1 mem_end)
    (hfin_lt : mem_end (lctNodesBase b - 1) + 1 < 2 ^ w) :
    ∃ x_tmp, LctMemRep w h L P b F x_tmp mem_end ∧ x_tmp.trees = trees1 := by
  have hle : mem_end (lctNodesBase b - 1) + 1 ≤ hp_caller + (mem_end (lctNodesBase b - 1) + 1) := by
    omega
  rcases exitOp_rep hrep₀ hfoot hhp_ge rfl hrep₀.valid hrep₀.edgeFits
      hz0_safe hpf0 hag0 hsafe hi.sf hi.hdrN hi.hdrCap hi.hdrL hi.hdrP
      hrep₀.edgeMap_snd_perm hrep₀.slots_perm hi.freeChain hi.freeNodeOk hi.vertexOk
      hi.edgeOk hi.auxPathOk hi.subdivOk hfin_lt hle (fun _ _ => rfl) with
    ⟨hrep_tmp, _, _⟩
  exact ⟨_, hrep_tmp, rfl⟩

private lemma re_exp_room_arith {s hp_eff phi0 phi1 cr ce m p2w : ℕ}
    (h1 : (s - hp_eff) + phi1 ≤ phi0 + cr) (hle : hp_eff ≤ s)
    (hbd : hp_eff + phi0 + (cr + ce) + m + 1 < p2w) :
    s + phi1 + ce + m < p2w := by
  omega

private lemma rerootExpose_arith {c_re c_exp s1 s2 hp_eff phi0 phi1 phi2 cr ce logN : ℕ}
    (h1 : c_re + (s1 - hp_eff) + phi1 ≤ phi0 + cr * logN)
    (h2 : c_exp + (s2 - s1) + phi2 ≤ phi1 + ce * logN)
    (hle1 : hp_eff ≤ s1) (hle2 : s1 ≤ s2) :
    (c_re + c_exp) + (s2 - hp_eff) + phi2 ≤ phi0 + (cr + ce) * logN := by
  have hexp : (cr + ce) * logN = cr * logN + ce * logN := Nat.add_mul cr ce logN
  omega

private lemma re_exp_fin_arith {c s hp0 phi0 phi2 cr m p2w : ℕ}
    (hc : c + (s - hp0) + phi2 ≤ phi0 + cr) (hle : hp0 ≤ s)
    (hbd : hp0 + phi0 + cr + m + 1 < p2w) : s + 1 < p2w := by
  omega

theorem rerootExpose_runs {w h L P b u v hp_caller hp_eff pos : ℕ}
    {F : MathForest} {x₀ : LctConc} (p : Program) (lp : LctProcs) (mem₀ : ℕ → ℕ)
    (hp_base : LctBaseOk w h L P p lp)
    (hp_sp : ∃ spB, lp.splay = SplayProcs.atBase spB)
    (hexpose_eq : p.procs[lp.expose]? = some (exposeBody lp.splay))
    (hrep₀ : LctMemRep w h L P b F x₀ mem₀)
    (hu : u < F.n) (hv : v < F.n)
    (hfoot : ∀ a, lctFoot b x₀ a → a < hp_caller)
    (hz₀ : ZeroFrom mem₀ hp_caller)
    (hhp_ge : hp_caller ≤ hp_eff)
    (hhp_bd : hp_eff + lctPhi L mem₀ b F.n +
      (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
      7000 * (L + 1) * (F.n + 2) + 1 < 2 ^ w)
    (ω : ℕ → Bool) :
    let nb := lctNodesBase b
    let cap := lctCap F.n
    let mem₁ := Function.update mem₀ (nb - 1) hp_eff
    ∃ st₁ st₂ c_re c_exp l₂ rest₂ x₂,
      Runs w p ω (lctRerootBody lp) (startState [nb, u + 1] mem₁ pos) (.returned 0) st₁ c_re ∧
      Runs w p ω (exposeBody lp.splay) (startState [nb, v + 1] st₁.mem st₁.pos) (.returned (v + 1)) st₂ c_exp ∧
      LctExposeInvs w h L P b F.n x₀.freeEdges x₀.edgeMap (.node (v + 1) l₂ .leaf :: rest₂) st₂.mem ∧
      SafeMem mem₁ nb cap hp_eff st₂.mem ∧
      ZeroFrom st₂.mem (st₂.mem (nb - 1)) ∧
      hp_eff ≤ st₂.mem (nb - 1) ∧
      nodeField st₂.mem nb (v + 1) OFF_PPAR = 0 ∧
      revFlag st₂.mem nb (v + 1) = false ∧
      nodeField st₂.mem nb (v + 1) OFF_HAS_TAG = 0 ∧
      (AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false =
        l₂.evalInorder (revFlag st₂.mem nb) false ++ [v + 1] ∧
      (F.SameComp u v →
        ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false).head? = some (u + 1)) ∧
      ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false).getLast? = some (v + 1) ∧
      (c_re + c_exp) + (st₂.mem (nb - 1) - hp_eff) + lctPhi L st₂.mem b F.n ≤
        lctPhi L mem₀ b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) ∧
      LctMemRep w h L P b F x₂ st₂.mem ∧
      x₂.trees = .node (v + 1) l₂ .leaf :: rest₂ ∧
      SlotZeroOk mem₁ nb ∧
      PtrFootOk b mem₁ x₀ L ∧
      (∀ a, a < b ∨ lctArenaHi b cap ≤ a ∧ a < hp_caller → mem₁ a = mem₀ a) ∧
      lctArenaHi b cap ≤ hp_eff ∧
      st₂.mem (nb - 1) + 1 < 2 ^ w ∧
      b + LCT_HDR_HP = nb - 1 ∧
      RootMove (lctAuxParent mem₀ nb cap) (lctAuxParent st₂.mem nb cap) cap (u + 1) := by
  dsimp only
  set nb := lctNodesBase b
  set cap := lctCap F.n
  set mem₁ := Function.update mem₀ (nb - 1) hp_eff
  have hhp_lt_w : hp_eff < 2 ^ w := by omega
  have hrep₀_hp := hrep₀.hp_le_of_foot hfoot
  have harena_hp : lctArenaHi b cap ≤ hp_caller := le_trans hrep₀_hp.1 hrep₀_hp.2.1
  have hbh_eq : b + LCT_HDR_HP = nb - 1 := by
    unfold nb lctNodesBase LCT_HDR_HP LCT_HDR_SIZE; omega
  rcases enterOp_invs hrep₀ hfoot hz₀ hhp_ge hhp_lt_w with
    ⟨hi0, hsafe0, hphi0_eq, hz0', hz0_safe, hpf0, hpar0, hag0⟩
  have hmem₁_hp : mem₁ (nb - 1) = hp_eff := Function.update_self _ _ _
  have harena_eff : lctArenaHi b cap ≤ hp_eff := le_trans harena_hp hhp_ge
  have hphi_m1 : lctPhi L mem₁ b F.n = lctPhi L mem₀ b F.n := hphi0_eq
  have hz0'' : ZeroFrom mem₁ (mem₁ (nb - 1)) := by simpa [mem₁, nb, hmem₁_hp] using hz0'
  have hmem₁_lt_re : mem₁ (nb - 1) + lctPhi L mem₁ b F.n +
      C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) < 2 ^ w := by
    rw [hmem₁_hp, hphi_m1]
    have hmul : C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) ≤
        (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hadd : hp_eff + lctPhi L mem₀ b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) +
          7000 * (L + 1) * (F.n + 2) <
        hp_eff + lctPhi L mem₀ b F.n + (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) +
          7000 * (L + 1) * (F.n + 2) + 1 := by
      exact Nat.lt_succ_of_le (by gcongr)
    exact lt_trans hadd hhp_bd
  have hedge_lt : ∀ q ∈ x₀.edgeMap, q.2.u < F.n ∧ q.2.v < F.n := fun q hq => by
    have hm : q.2 ∈ x₀.edgeMap.map Prod.snd := List.mem_map.2 ⟨q, hq, rfl⟩
    have hf : q.2 ∈ F.edges := hrep₀.edgeMap_snd_perm.mem_iff.1 hm
    exact ⟨(hrep₀.valid.1 q.2 hf).1, (hrep₀.valid.1 q.2 hf).2.1⟩
  have hslots : ∀ a, F.n + 1 ≤ a → a ≤ cap → a ∈ x₀.freeEdges ∨ ∃ q ∈ x₀.edgeMap, q.1 = a := by
    intro a ha1 ha2
    dsimp only [cap, lctCap] at ha2
    have hrng : a ∈ (List.range F.n).map (F.n + 1 + ·) :=
      List.mem_map.2 ⟨a - (F.n + 1), List.mem_range.2 (by omega), by omega⟩
    have hm := hrep₀.slots_perm.symm.mem_iff.1 hrng
    rcases List.mem_append.1 hm with hf | hfr
    · rcases List.mem_map.1 hf with ⟨q, hq, rfl⟩
      exact Or.inr ⟨q, hq, rfl⟩
    · exact Or.inl hfr
  rcases lctRerootBody_runs p lp mem₁ mem₁ hp_base hp_sp hexpose_eq hz0_safe
      harena_eff hsafe0 hi0 hu hz0'' hedge_lt hslots hmem₁_lt_re ω with
    ⟨st₁, c_re, _, _, hrun_re, hi₁, hsafe₁, hfr₁, _, hpar1_zero, hsame1, hmove1, hphi₁⟩
  have hle_re : hp_eff ≤ st₁.mem (nb - 1) := by
    have h1 : mem₁ (nb - 1) ≤ st₁.mem (nb - 1) := hfr₁.2.2.1
    simpa [hmem₁_hp] using h1
  have hz₁ : ZeroFrom st₁.mem (st₁.mem (nb - 1)) := hfr₁.2.2.2.2.1
  have hst₁_lt_exp : st₁.mem (nb - 1) + lctPhi L st₁.mem b F.n +
      C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) + 7000 * (L + 1) * (F.n + 2) < 2 ^ w := by
    have hphi_re : (st₁.mem (nb - 1) - hp_eff) + lctPhi L st₁.mem b F.n ≤
        lctPhi L mem₀ b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) := by
      have hh := hphi₁
      change c_re + (st₁.mem (nb - 1) - mem₁ (nb - 1)) + lctPhi L st₁.mem b F.n ≤
        lctPhi L mem₁ b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) at hh
      rw [hmem₁_hp, hphi_m1] at hh; omega
    have hexp_mul : (C_REROOT_OP L + C_EXPOSE_OP L) * (Nat.log 2 (F.n + 2) + 1) =
        C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) + C_EXPOSE_OP L * (Nat.log 2 (F.n + 2) + 1) :=
      Nat.add_mul _ _ _
    rw [hexp_mul] at hhp_bd
    exact re_exp_room_arith hphi_re hle_re hhp_bd
  rcases exposeBody_runs p lp.splay mem₁ st₁.mem hp_base.splay_hasAt hp_sp hp_base.splay_ok
      hz0_safe harena_eff hsafe₁ hi₁ hv hz₁ hst₁_lt_exp ω with
    ⟨st₂, c_exp, l₂, rest₂, hrun_exp, hi₂, hsafe₂, hfr₂, hpar₂, hpp₂, hrev₂, hht₂, hev₂, hphi₂⟩
  have hle_exp : st₁.mem (nb - 1) ≤ st₂.mem (nb - 1) := hfr₂.2.2.1
  have hz₂ : ZeroFrom st₂.mem (st₂.mem (nb - 1)) := hfr₂.2.2.2.2.1
  have hphi_re' : c_re + (st₁.mem (nb - 1) - hp_eff) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₀ b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) := by
    have hh := hphi₁
    change c_re + (st₁.mem (nb - 1) - mem₁ (nb - 1)) + lctPhi L st₁.mem b F.n ≤
      lctPhi L mem₁ b F.n + C_REROOT_OP L * (Nat.log 2 (F.n + 2) + 1) at hh
    rwa [hmem₁_hp, hphi_m1] at hh
  have hcost_re_exp := rerootExpose_arith hphi_re' hphi₂ hle_re hle_exp
  have hfin_lt : st₂.mem (nb - 1) + 1 < 2 ^ w :=
    re_exp_fin_arith (by dsimp only [nb] at hcost_re_exp ⊢; exact hcost_re_exp)
      (le_trans hle_re hle_exp) hhp_bd
  rcases mem_of_exposeInvs hrep₀ hfoot hhp_ge hz0_safe hpf0 hag0 hsafe₂ hi₂ hfin_lt with
    ⟨x₂, hrep₂, hx2_trees⟩
  have hlast_v :
      ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false).getLast? =
        some (v + 1) := by
    rw [hev₂]; simp
  have hhead_same : F.SameComp u v →
      ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false).head? =
        some (u + 1) := by
    intro hsc
    have hne :
        (AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false ≠ [] := by
      rw [hev₂]; simp
    cases hhd : ((AuxTree.node (v + 1) l₂ .leaf).evalInorder (revFlag st₂.mem nb) false).head? with
    | none => exact absurd (List.head?_eq_none_iff.1 hhd) hne
    | some r =>
        have hr_ra := head_evalInorder_eq_rootAbove hi₂ hpp₂ hlast_v hhd
        have hpar_fun : lctAuxParent st₂.mem nb cap = lctAuxParent st₁.mem nb cap :=
          funext fun z => hpar₂ z
        have hu1 : 1 ≤ u + 1 := by omega
        have hu2 : u + 1 ≤ cap := by unfold cap lctCap; omega
        have hv1 : 1 ≤ v + 1 := by omega
        have hv2 : v + 1 ≤ cap := by unfold cap lctCap; omega
        have hiff0 := (hrep₀.sameComp_iff_rootAbove hu hv).1 hsc
        have hpar_fun0 : lctAuxParent mem₁ nb cap = lctAuxParent mem₀ nb cap :=
          funext fun z => hpar0 z
        have hsc1 : rootAbove (lctAuxParent mem₁ nb cap) cap (u + 1) =
            rootAbove (lctAuxParent mem₁ nb cap) cap (v + 1) := by
          simpa [hpar_fun0] using hiff0
        have hsc_st1 := (hsame1 (u + 1) (v + 1) hu1 hu2 hv1 hv2).mpr hsc1
        have hroot_u : rootAbove (lctAuxParent st₁.mem nb cap) cap (u + 1) = u + 1 := by
          cases hc : cap with
          | zero => omega
          | succ m =>
              unfold rootAbove
              have hp0 : lctAuxParent st₁.mem nb (m + 1) (u + 1) = 0 := by
                dsimp only [nb, cap] at hc ⊢; rw [← hc]; exact hpar1_zero
              simp [hp0]
        have hr_eq : r = u + 1 := by
          rw [hr_ra, hpar_fun, ← hsc_st1, hroot_u]
        rw [hr_eq]
  refine ⟨st₁, st₂, c_re, c_exp, l₂, rest₂, x₂, hrun_re, hrun_exp, hi₂, hsafe₂,
    hz₂, le_trans hle_re hle_exp, hpp₂, hrev₂, hht₂, hev₂, hhead_same, hlast_v, hcost_re_exp,
    hrep₂, hx2_trees, hz0_safe, hpf0, hag0, harena_eff, hfin_lt, hbh_eq, ?_⟩
  have hfun2 : lctAuxParent st₂.mem nb cap = lctAuxParent st₁.mem nb cap := funext fun z => hpar₂ z
  have hfun0 : lctAuxParent mem₁ nb cap = lctAuxParent mem₀ nb cap := funext fun z => hpar0 z
  rw [hfun2, ← hfun0]
  exact hmove1

end PathSetupHelpers

section RerootRootsDef

open Classical

/-- After an operation that rerooted `u`: the tree of `u` has root `u`, and every other vertex
keeps its root. Roots are read with `lctCanonRoot`. -/
noncomputable def RerootRoots (mem₀ mem' : ℕ → ℕ) (b : ℕ) (F : MathForest) (u : ℕ) : Prop :=
  ∀ v < F.n, lctCanonRoot mem' b F.n v = if F.SameComp v u then u else lctCanonRoot mem₀ b F.n v

theorem LctMemRep.rerootRoots_of_rootMove {w h L P b u : ℕ} {F : MathForest} {x : LctConc}
    {mem₀ mem' : ℕ → ℕ} (hrep₀ : LctMemRep w h L P b F x mem₀) (hu : u < F.n)
    (hmove : RootMove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n))
      (lctAuxParent mem' (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (u + 1)) :
    RerootRoots mem₀ mem' b F u := by
  intro v hv
  have hm := hmove (v + 1) (by omega) (by unfold lctCap; omega)
  have hiff := hrep₀.sameComp_iff_rootAbove hv hu
  unfold lctCanonRoot
  rw [hm]
  by_cases hs : F.SameComp v u
  · have h2 := hiff.1 hs
    simp only [h2, hs, ↓reduceIte, Nat.add_sub_cancel]
  · have h2 : ¬ rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (v + 1) =
        rootAbove (lctAuxParent mem₀ (lctNodesBase b) (lctCap F.n)) (lctCap F.n) (u + 1) :=
      fun h => hs (hiff.2 h)
    simp only [h2, hs, ↓reduceIte]

theorem rootMove_of_agree {par₀ par₁ par₂ : ℕ → ℕ} {cap r : ℕ}
    (hm : RootMove par₀ par₁ cap r) (hag : ∀ z, par₂ z = par₁ z) : RootMove par₀ par₂ cap r := by
  have : par₂ = par₁ := funext hag
  rw [this]; exact hm

end RerootRootsDef

end MinCostFlow.LinkCut.Prog
